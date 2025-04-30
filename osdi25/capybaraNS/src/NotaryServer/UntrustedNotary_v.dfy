/// This file contains the implementation of `UntrustedNotary`, i.e.,
/// the main logic for the notary server. It's untrusted in that it
/// doesn't have to be read by the auditor to be sure of the notary's
/// correctness; the fact that it passes verification is sufficient.
///
/// It's invoked by `TrustedNotary`, which ensures that
/// `UntrustedNotary` is correct by relying only on the preconditions
/// and postconditions of `UntrustedNotary` methods. To verify that
/// `UntrustedNotary` is not only functionally correct but also
/// crash-consistent, the trusted notary attaches PoWER restrictions
/// to storage before passing that storage to the untrusted notary.
/// For instance, when invoking the `Advance` method that advances the
/// notary's counter, it restricts writes such that all intermediate
/// crash states must be proven to recover to either the pre-state or
/// the post-state of the specification for the `Advance` operation.

include "../Framework/ExternalMethods_t.dfy"
include "../Framework/NativeTypes_t.dfy"
include "../Framework/PersistentMemory_t.dfy"
include "../Framework/PmemUtil_v.dfy"
include "Advance_v.dfy"
include "Layout_v.dfy"
include "NotarySpec_t.dfy"
include "Setup_v.dfy"
include "Start_v.dfy"
include "Util_v.dfy"

module UntrustedNotaryModule {
import opened ExternalMethodsModule
import opened PersistentMemoryModule
import opened PmemUtilModule
import opened NativeTypesModule
import opened NotaryAdvanceModule
import opened NotaryLayoutModule
import opened NotarySetupModule
import opened NotaryStartModule
import opened NotarySpecModule
import opened NotaryUtilModule

class UntrustedNotary
{
    static const SPACE_NEEDED_NOT_INCLUDING_KEY: int := KEY_PAIR_POS as int

    var keyPair: KeyPair          // the key pair used for signing
    var counter: uint64           // the current value of the monotonic counter
    var cdb: bool                 // the current corruption-detecting boolean
    var crcDigest: CrcDigest      // an external object used for computing CRCs
    var myBuffer: array<byte>     // buffer used for storing the following data:
                                  //     first 8 bytes   - temporary storage for CRCs and CDBs,
                                  //     next 8 bytes    - serialization of current counter
                                  //     remaining bytes - last message notarized

    // This is the set of heap objects that are reachable from this object.
    ghost function Repr() : set<object>
        reads this
    {
        { this, keyPair, crcDigest, myBuffer }
    }

    // This is the invariant that this object maintains, in relation to the contents of the
    // persistent memory region.
    ghost predicate Valid(pmv: PersistentMemoryRegionView)
        reads Repr()
    {
        && PmvValid(pmv)
        && pmv.readState == pmv.durableState             // it's been flushed
        && Recover(pmv.durableState).Some?               // it recovers to a valid state
        && cdb == RecoverCDB(pmv.durableState).value     // `cdb` reflects what it will be on recovery
        && var state := Recover(pmv.durableState).value;
        && state.counter == counter                      // `counter` reflects what it will be on recovery
        && state.key == keyPair.View()                   // `keyPair` holds our public/private key pair
        && myBuffer.Length == CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH
        && myBuffer[CRC_SIZE .. CRC_SIZE + SIZEOF_UINT64] == SpecSerializeUint64(counter)
        && myBuffer[CRC_SIZE + SIZEOF_UINT64 .. CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH] ==
              state.lastMessage
    }

    // This is the recovery routine, describing whether and how we can recover our
    // state from persistent memory.
    static ghost function Recover(state: seq<byte>) : Option<NotaryServerState>
    {
        RecoverNotaryState(state)
    }

    // This is just a simple constructor that copies every field from inputs.
    constructor(
        i_keyPair: KeyPair,
        i_counter: uint64,
        i_cdb: bool,
        i_crcDigest: CrcDigest,
        i_myBuffer: array<byte>
    )
        ensures keyPair == i_keyPair
        ensures counter == i_counter
        ensures cdb == i_cdb
        ensures crcDigest == i_crcDigest
        ensures myBuffer == i_myBuffer
    {
        keyPair := i_keyPair;
        counter := i_counter;
        cdb := i_cdb;
        crcDigest := i_crcDigest;
        myBuffer := i_myBuffer;
    }

    // This method sets up persistent memory to hold notary state. It returns a boolean indicating
    // whether it succeeded.
    static method Setup(pmem: PersistentMemoryRegion) returns (success: bool)
        requires pmem.Valid()
        requires forall s :: s in pmem.StatesPermitted()  // it must be given permission to crash in arbitrary states
        modifies pmem
        ensures  pmem.Valid()
        ensures  SetupCorrect(if success then Recover(pmem.View().durableState) else None, PmvLen(pmem.View()),
                              SPACE_NEEDED_NOT_INCLUDING_KEY, pmem.constants.imperviousToCorruption)
    {
        pmem.Axiom_ImplicationsOfValid();
        var regionSize := pmem.GetRegionSize();

        // Generate key pair and serialize it

        var keyPair := KeyPair.Generate();
        var keyPairBytes := keyPair.SerializePrivateKey();

        // Check that sufficient space exists in the region.

        var keyPairLength := keyPairBytes.Length as int32;
        if regionSize < KEY_PAIR_POS as int64 {
            return false;
        }
        if regionSize - KEY_PAIR_POS as int64 < keyPairLength as int64 {
            return false;
        }

        // Serialize everything but the key pair into a fresh byte array `bytes`

        var bytes := new byte[KEY_PAIR_POS];
        ExternalMethods.SerializeUint64(CDB_FALSE, bytes, CDB_POS);
        ExternalMethods.SerializeUint64(0, bytes, COUNTER_POS0);
        ZeroRange(bytes, LAST_MESSAGE_POS0, NOTARIZED_MESSAGE_LENGTH_INT32);
        assert bytes[LAST_MESSAGE_POS0 as int .. LAST_MESSAGE_POS0 as int + NOTARIZED_MESSAGE_LENGTH] ==
               SequenceOfZeroes(NOTARIZED_MESSAGE_LENGTH);
        ExternalMethods.SerializeUint64(keyPairLength as uint64, bytes, KEY_PAIR_LENGTH_POS);

        // Compute CRCs and put them in the appropriate places in `bytes`
        
        var crcDigest := CrcDigest.Create();
        crcDigest.Add(bytes, COUNTER_POS0, SIZEOF_UINT64_INT32 + NOTARIZED_MESSAGE_LENGTH_INT32);
        assert crcDigest.View() ==
               bytes[COUNTER_POS0..COUNTER_POS0 + SIZEOF_UINT64_INT32 + NOTARIZED_MESSAGE_LENGTH_INT32];
        crcDigest.Compute(bytes, DATA_CRC_POS0);

        crcDigest.Reset();
        crcDigest.Add(bytes, KEY_PAIR_LENGTH_POS, SIZEOF_UINT64_INT32);
        assert crcDigest.View() == bytes[KEY_PAIR_LENGTH_POS .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64];
        crcDigest.Compute(bytes, KEY_PAIR_LENGTH_CRC_POS);

        crcDigest.Reset();
        crcDigest.Add(keyPairBytes, 0, keyPairLength);
        assert crcDigest.View() == keyPairBytes[..];
        crcDigest.Compute(bytes, KEY_PAIR_CRC_POS);

        // Write `bytes` and the key pair to persistent memory

        pmem.Write(0, bytes, 0, KEY_PAIR_POS);
        pmem.Write(KEY_PAIR_POS as int64, keyPairBytes, 0, keyPairLength);
        pmem.Flush();

        // Invoke `Lemma_SetupHelper` to establish postconditions

        Lemma_SetupHelper(bytes[..], keyPair.View(), keyPairBytes[..], pmem.View().durableState[..]);
        return true;
    }

    // This method recovers the notary server state from persistent memory and creates an
    // `UntrustedNotary` object initialized with that state.
    static method {:timeLimitMultiplier 4} Start(wrpm: PersistentMemoryRegion) returns (result: UntrustedNotary?)
        requires wrpm.Valid()
        requires Recover(wrpm.View().durableState).Some?
        requires forall s: seq<byte> :: Recover(s) == Recover(wrpm.View().durableState) ==> s in wrpm.StatesPermitted()
        modifies wrpm
        ensures  wrpm.Valid()
        ensures  Recover(wrpm.View().durableState) == old(Recover(wrpm.View().durableState))
        ensures  result != null ==> wrpm !in result.Repr()
        ensures  result != null ==> result.Valid(wrpm.View())
        ensures  result == null ==> !wrpm.constants.imperviousToCorruption
    {
        wrpm.Axiom_ImplicationsOfValid();
        ghost var state := wrpm.View().durableState;

        // Get the region size and make sure it's big enough to read the header from.
        // This is just for paranoia; it's technically not necessary.
        var regionSize := wrpm.GetRegionSize();
        assert |state| == regionSize as int;
        if regionSize < KEY_PAIR_POS as int64 {
            assert false;
            return null;
        }

        // Before we start reading, flush to make sure that we'll read the durable state.
        wrpm.Flush();

        // Allocate a buffer `bytes` to read the header (the first `KEY_PAIR_POS` bytes) into.
        var bytes := new byte[KEY_PAIR_POS];
        wrpm.Read(0, bytes, 0, KEY_PAIR_POS);
        assert bytes[..] == bytes[0..KEY_PAIR_POS];

        // Compute the CDB.

        var cdbValue := ExternalMethods.DeserializeUint64(bytes, CDB_POS);
        assert wrpm.constants.imperviousToCorruption ==>
               state[CDB_POS as int .. CDB_POS as int + SIZEOF_UINT64] ==
               bytes[CDB_POS as int .. CDB_POS as int + SIZEOF_UINT64];
        if cdbValue != CDB_FALSE && cdbValue != CDB_TRUE {
            // If the CDB is not a valid value, the read must have read corrupted data.
            // Call `Lemma_StartHelper1` to learn that and thus enable returning `null`.
            Lemma_StartHelper1(state, bytes[..], wrpm.constants.imperviousToCorruption, cdbValue);
            return null;
        }
        var cdb := cdbValue == CDB_TRUE;
        assert cdb == RecoverCDB(state).value by {
            // If the CDB is a valid value, we know that it's uncorrupted and we can compute
            // the actual value of `cdb` from it. Call `Lemma_StartHelper2` to learn that it's
            // uncorrupted.
            Lemma_StartHelper2(state, bytes[..], wrpm.constants.imperviousToCorruption, cdbValue, cdb);
        }

        // Allocate `myBuffer` as a place to store bytes both now and throughout the operation
        // of the notary server. Also allocate `crcDigest`, an object used for computing CRCs.

        var myBuffer := new byte[SIZEOF_UINT64 + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH];
        var crcDigest := CrcDigest.Create();

        // Compute the CRC of the data (counter and last message) and check it.

        var dataPos: int32 := if cdb then COUNTER_POS1 else COUNTER_POS0;
        var crcPos: int32 := if cdb then DATA_CRC_POS1 else DATA_CRC_POS0;
        crcDigest.Add(bytes, dataPos, SIZEOF_UINT64_INT32 + NOTARIZED_MESSAGE_LENGTH_INT32);
        assert crcDigest.View() == bytes[dataPos .. dataPos + SIZEOF_UINT64_INT32 + NOTARIZED_MESSAGE_LENGTH_INT32];
        crcDigest.Compute(myBuffer, 0);

        var crcMatches := CompareArrays(myBuffer, bytes, 0, crcPos, CRC_SIZE_INT32);
        if !crcMatches {
            // If the CRC we compute doesn't match what we read from storage, we must have corruption.
            // Call `Lemma_StartHelper3` to learn that and thus enable returning `null`.
            Lemma_StartHelper3(state, bytes[..], wrpm.constants.imperviousToCorruption, cdb, dataPos as int,
                               crcPos as int, myBuffer[0..CRC_SIZE]);
            assert !wrpm.constants.imperviousToCorruption;
            return null;
        }

        var messagePos: int32 := if cdb then LAST_MESSAGE_POS1 else LAST_MESSAGE_POS0;
        assert && bytes[dataPos as int .. dataPos as int + SIZEOF_UINT64] ==
                  state[dataPos as int .. dataPos as int + SIZEOF_UINT64]
               && bytes[messagePos as int .. messagePos as int + NOTARIZED_MESSAGE_LENGTH] ==
                  state[messagePos as int .. messagePos as int + NOTARIZED_MESSAGE_LENGTH] by {
            // Since the CRC did match what was read from storage, we can conclude that the
            // data (counter and last message) are uncorrupted. Call `Lemma_StartHelper4` to learn
            // this and enable using those parts of `bytes` as authoritative.
            Lemma_StartHelper4(state, bytes[..], wrpm.constants.imperviousToCorruption, cdb,
                               dataPos as int, crcPos as int, messagePos as int, myBuffer[0..CRC_SIZE]);
        }

        // Deserialize the counter from the beginning of the data region we just validated, and
        // store the result in `counter`. Also, copy it into `myBuffer[CRC_SIZE .. CRC_SIZE + UINT64_SIZE]`
        // to maintain the invariant that those bytes contain the serialization of the current
        // counter.

        var counter := ExternalMethods.DeserializeUint64(bytes, dataPos);
        assert counter == SpecDeserializeUint64(state[dataPos as int .. dataPos as int + SIZEOF_UINT64]);
        Axiom_SerializeDeserializeUint64(counter);
        Axiom_DeserializeSerializeUint64(state[dataPos as int .. dataPos as int + SIZEOF_UINT64]);
        assert Some(counter) == RecoverCounter(cdb, state);
        CopyArray(myBuffer, bytes, CRC_SIZE_INT32, dataPos, SIZEOF_UINT64_INT32);
        assert myBuffer[CRC_SIZE .. CRC_SIZE + SIZEOF_UINT64] == SpecSerializeUint64(counter);

        // Copy the last message from the data region we just validated to maintain the invariant that
        // we always keep the last message in:
        // `myBuffer[CRC_SIZE + SIZEOF_UINT64 .. CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH]`.

        var lastMessagePos := if cdb then LAST_MESSAGE_POS1 else LAST_MESSAGE_POS0;
        CopyArray(myBuffer, bytes, CRC_SIZE_INT32 + SIZEOF_UINT64_INT32, lastMessagePos,
                  NOTARIZED_MESSAGE_LENGTH_INT32);
        assert myBuffer[CRC_SIZE + SIZEOF_UINT64 .. CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH] ==
               RecoverLastMessage(cdb, state);

        // Compute the CRC of the bytes purporting to contain the length of the key pair. Then compare
        // that to the bytes purporting to contain that CRC in storage.

        crcDigest.Reset();
        crcDigest.Add(bytes, KEY_PAIR_LENGTH_POS, SIZEOF_UINT64_INT32);
        assert crcDigest.View() == bytes[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64];
        crcDigest.Compute(myBuffer, 0);
        crcMatches := CompareArrays(myBuffer, bytes, 0, KEY_PAIR_LENGTH_CRC_POS, CRC_SIZE_INT32);
        if !crcMatches {
            // If the CRCs don't match, we must have a corrupted storage. Call `Lemma_StartHelper5` to
            // establish that and thereby enable returning `null`.
            Lemma_StartHelper5(state, bytes[..], wrpm.constants.imperviousToCorruption, myBuffer[0..CRC_SIZE]);
            assert !wrpm.constants.imperviousToCorruption;
            return null;
        }

        // Since the CRCs do match, we know the read was uncorrupted. Call `Lemma_StartHelper6` to
        // establish that and enable using the bytes as authoritative. Then deserialize those bytes
        // to get the key pair length.
        assert bytes[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64] ==
               state[KEY_PAIR_LENGTH_POS as int .. KEY_PAIR_LENGTH_POS as int + SIZEOF_UINT64] by {
            Lemma_StartHelper6(state, bytes[..], wrpm.constants.imperviousToCorruption, myBuffer[0..CRC_SIZE]);
        }
        var keyPairLength := ExternalMethods.DeserializeUint64(bytes, KEY_PAIR_LENGTH_POS);
        assert keyPairLength == RecoverKeyPairLength(state).value;

        // Make sure that the region is big enough to read the key pair from. This is technically
        // not necessary because it should never happen, but we check it for paranoia.
        if regionSize - KEY_PAIR_POS as int64 < keyPairLength as int64 {
            assert false;
            return null;
        }
        if keyPairLength > 0x7FFF_FFFF {
            assert false;
            return null;
        }

        // Read the serialized key pair from storage as well as the CRC of the key pair.
        // Then compute the CRC of the key pair serialization and compare it to the CRC read
        // from storage.
        var keyPairBytes := new byte[keyPairLength];
        wrpm.Read(KEY_PAIR_POS as int64, keyPairBytes, 0, keyPairLength as int32);
        assert keyPairBytes[..] == keyPairBytes[0..keyPairLength as int];
        crcDigest.Reset();
        crcDigest.Add(keyPairBytes, 0, keyPairLength as int32);
        assert crcDigest.View() == keyPairBytes[..];
        crcDigest.Compute(myBuffer, 0);

        crcMatches := CompareArrays(myBuffer, bytes, 0, KEY_PAIR_CRC_POS, SIZEOF_UINT64_INT32);
        if !crcMatches {
            // If the CRCs don't match, we must have a corrupted storage. Call `Lemma_StartHelper7` to
            // establish that and thereby enable returning `null`.
            Lemma_StartHelper7(state, bytes[..], wrpm.constants.imperviousToCorruption, keyPairLength,
                               keyPairBytes[..], myBuffer[0..CRC_SIZE]);
            assert !wrpm.constants.imperviousToCorruption;
            return null;
        }

        // Since the CRC matches, we can conclude that the data is uncorrupted and start using it as
        // authoritative. We deserialize the key pair into `keyPair`.
        assert keyPairBytes[0..keyPairLength as int] ==
               state[KEY_PAIR_POS as int .. KEY_PAIR_POS as int + keyPairLength as int] by {
            Lemma_StartHelper8(state, bytes[..], wrpm.constants.imperviousToCorruption, keyPairLength,
                               keyPairBytes[..], myBuffer[0..CRC_SIZE]);
        }
        var keyPair := KeyPair.DeserializePrivateKey(keyPairBytes, 0, keyPairLength as int32);
        assert keyPair.View() == RecoverKeyPair(state, keyPairLength).value;

        assert(myBuffer[CRC_SIZE .. CRC_SIZE + SIZEOF_UINT64] == SpecSerializeUint64(counter));
        // We have everything we need to create an `UntrustedNotary` object.
        return new UntrustedNotary(keyPair, counter, cdb, crcDigest, myBuffer);
    }

    // This method returns the serialization of the public key part of our public/private key pair.
    method ExtractPublicKey(wrpm: PersistentMemoryRegion) returns (publicKey: array<byte>)
        requires wrpm.Valid()
        requires this.Valid(wrpm.View())
        requires wrpm !in Repr()
        ensures  Recover(wrpm.View().durableState).Some?
        ensures  SpecPublicKeySerializationCorrect(Recover(wrpm.View().durableState).value.key.publicKey, publicKey[..])
    {
        publicKey := keyPair.SerializePublicKey();
    }

    // This method returns the current value of the monotonic counter.
    method ReadCounter(wrpm: PersistentMemoryRegion) returns (counter: uint64)
        requires wrpm.Valid()
        requires this.Valid(wrpm.View())
        requires wrpm !in Repr()
        ensures  Recover(wrpm.View().durableState).Some?
        ensures  counter == Recover(wrpm.View().durableState).value.counter
    {
        counter := this.counter;
    }

    // This method returns the last message notarized by the notary server.
    method ReadMessage(wrpm: PersistentMemoryRegion) returns (message: array<byte>)
        requires wrpm.Valid()
        requires this.Valid(wrpm.View())
        requires wrpm !in Repr()
        ensures  fresh(message)
        ensures  Recover(wrpm.View().durableState).Some?
        ensures  message[..] == Recover(wrpm.View().durableState).value.lastMessage
    {
        // We have an invariant that the last message is always stored in the last part of `myBuffer`.
        // So we allocate a fresh array and copy it into there.
        message := new byte[NOTARIZED_MESSAGE_LENGTH];
        CopyArray(message, myBuffer, 0, CRC_SIZE_INT32 + SIZEOF_UINT64_INT32, NOTARIZED_MESSAGE_LENGTH_INT32);
    }

    // This method advances the counter and associates the given message with that new
    // counter value. One input is the PoWER-restricted persistent memory region
    // that obligates us to only crash into permitted states. Specifically, we're
    // only allowed to write to storage if we prove that any resulting crash state
    // is permitted. A state is permitted if it recovers to either the pre-state
    // or the post-state of the advance operation. For instance, we're not allowed
    // to crash in a state where the counter has advanced but the message hasn't
    // changed.
    method Advance(wrpm: PersistentMemoryRegion, message: array<byte>) returns (success: bool)
        requires wrpm.Valid()
        requires this.Valid(wrpm.View())
        requires wrpm !in Repr()
        requires
            // We're permitted to crash into two types of state:
            // (1) The state recovers to the same state we recover to now.
            // (2) The state recovers to what results from an atomic completion of the advance operation.
            var state := Recover(wrpm.View().durableState);
            && state.Some?
            && (forall s: seq<byte> :: Recover(s) == state ==> s in wrpm.StatesPermitted())
            && (forall s: seq<byte> ::
                Recover(s).Some? && AdvanceCorrect(state.value, Recover(s).value, message[..], true, true) ==>
                s in wrpm.StatesPermitted())
        modifies wrpm
        modifies this.Repr()
        ensures  wrpm.Valid()
        ensures  this.Valid(wrpm.View())
        ensures  wrpm !in Repr()
        ensures
            // On return, we must have changed the state of the persistent memory so that it will
            // crash into a state that results from the completion of the advance operation.
            var state := old(Recover(wrpm.View().durableState));
            var state' := Recover(wrpm.View().durableState);
            && state.Some?
            && state'.Some?
            && AdvanceCorrect(state.value, state'.value, message[..], wrpm.constants.imperviousToCorruption, success)
    {
        // If the counter is maxed out, we may (and must) return false.
        if counter == 0xFFFF_FFFF_FFFF_FFFF {
            return false;
        }

        // If we're being asked to notarize a message of the wrong length, we may (and must) return false.
        if message.Length != NOTARIZED_MESSAGE_LENGTH {
            return false;
        }
        
        // Increment the counter and serialize it to the appropriate place in `myBuffer`.
        counter := counter + 1;
        ExternalMethods.SerializeUint64(counter, myBuffer, CRC_SIZE_INT32);
        assert myBuffer[CRC_SIZE .. CRC_SIZE + SIZEOF_UINT64] == SpecSerializeUint64(counter);
        Axiom_SerializeDeserializeUint64(counter);

        // Copy the message into the appropriate place in `myBuffer`.

        CopyArray(myBuffer, message, CRC_SIZE_INT32 + SIZEOF_UINT64_INT32, 0, NOTARIZED_MESSAGE_LENGTH_INT32);
        assert message[..] == message[0..NOTARIZED_MESSAGE_LENGTH];
        assert myBuffer[CRC_SIZE + SIZEOF_UINT64 .. CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH] == message[..];

        // Compute the CRC of the data (counter and last message) and store it at the beginning of `myBuffer`.
        crcDigest.Reset();
        crcDigest.Add(myBuffer, CRC_SIZE_INT32, SIZEOF_UINT64_INT32 + NOTARIZED_MESSAGE_LENGTH_INT32);
        assert crcDigest.View() == myBuffer[CRC_SIZE .. CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH];
        crcDigest.Compute(myBuffer, 0);

        // Write the entirety of `myBuffer` (containing the CRC, counter, and last message) to the
        // place in storage corresponding to the inactive CDB. Since `cdb` is the active one,
        // `!cdb` is the inactive one. We call `Lemma_AdvanceHelper1` to establish that the
        // write we're doing only affects data unreachable during recovery and is thus permitted.
        var unusedCrcPos := if cdb then DATA_CRC_POS0 else DATA_CRC_POS1;
        lemma_AdvanceHelper1(wrpm, cdb, myBuffer[..], unusedCrcPos as int);
        wrpm.Write(unusedCrcPos as int64, myBuffer, 0,
                   CRC_SIZE_INT32 + SIZEOF_UINT64_INT32 + NOTARIZED_MESSAGE_LENGTH_INT32);

        // Flush the storage to make sure the write is durable.
        wrpm.Flush();

        // Compute the serialized CDB value corresponding to `!cdb` so we can write it to
        // the CDB position in storage. We call `Lemma_AdvanceHelper2` to establish
        // that this write is atomic and can only crash into a single new state, the one that
        // results from writing it completely. That lemma also establishes that this new state
        // is the one we want, i.e., one for which recovery will yield the updated counter and
        // new message.
        assert(wrpm.View().durableState == UpdateBytes(old(wrpm.View().durableState),
                                                       (if cdb then DATA_CRC_POS0 else DATA_CRC_POS1) as int,
                                                       myBuffer[..]));
        lemma_AdvanceHelper2(wrpm, old(wrpm.View().durableState), wrpm.View().durableState, cdb,
                             counter, message[..], myBuffer[..]);
        var newCdbValue := if cdb then CDB_FALSE else CDB_TRUE;
        ExternalMethods.SerializeUint64(newCdbValue, myBuffer, 0);
        Lemma_WritingAlignedChunkPermittedIfFullWritePermitted(wrpm, CDB_POS as int, myBuffer[0..CRC_SIZE]);
        wrpm.Write(CDB_POS as int64, myBuffer, 0, CRC_SIZE_INT32);

        // Show that this write of the CDB didn't affect the parts of `myBuffer` we
        // care about maintaining for our invariant.
        assert myBuffer[CRC_SIZE .. CRC_SIZE + SIZEOF_UINT64] == SpecSerializeUint64(counter);
        assert myBuffer[CRC_SIZE + SIZEOF_UINT64 .. CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH] ==
               message[..];

        // Flush the storage to make sure the write is durable, i.e., the only possible
        // crash state is the one where the write has completed. That way, we know we're
        // in the post-advance state and can satisfy the postcondition requiring the
        // advance operation to have completed.
        wrpm.Flush();

        // Update the active CDB and return true to indicate success.
        cdb := !cdb;

        return true;
    }

    // This method signs the current counter value and last notarized message, and returns a
    // fresh array containing the signature.
    method Sign(wrpm: PersistentMemoryRegion) returns (signature: array<byte>)
        requires wrpm.Valid()
        requires this.Valid(wrpm.View())
        requires wrpm !in Repr()
        modifies this.Repr()
        ensures  this.Valid(wrpm.View())
        ensures  wrpm !in Repr()
        ensures  Recover(wrpm.View().durableState).Some?
        ensures  SignCorrect(Recover(wrpm.View().durableState).value, signature[..])
    {
        // We have an invariant that the data to be signed is already in `myBuffer` starting
        // at position `CRC_SIZE`. So we just need to sign that data.
        ghost var state := Recover(wrpm.View().durableState).value;
        assert myBuffer[CRC_SIZE .. CRC_SIZE + SIZEOF_UINT64 + NOTARIZED_MESSAGE_LENGTH] ==
               SpecSerializeUint64(counter) + state.lastMessage;
        signature := keyPair.Sign(myBuffer, CRC_SIZE_INT32, CRC_SIZE_INT32 + NOTARIZED_MESSAGE_LENGTH_INT32);
    }
}

}
