/// This file contains the trusted specification of the notary
/// service. Since it's a trusted file, an auditor must read and check
/// it; it's not sufficient to just verify it. The file describes the
/// abstract state of the notary service, its legal initial states,
/// and the semantics of each function in the service's interface
/// (advance and sign).
///
include "../Framework/ExternalMethods_t.dfy"
include "../Framework/NativeTypes_t.dfy"
include "../Framework/PersistentMemory_t.dfy"

module NotarySpecModule {
import opened ExternalMethodsModule
import opened NativeTypesModule
import opened PersistentMemoryModule

// The state consists of a key pair, a counter, and the last message
// received for notarization. That last message is associated with the
// current counter value.

datatype NotaryServerState = NotaryServerState(key: KeyView, counter: uint64, lastMessage: seq<byte>)

datatype Option<T> = None | Some(value: T)

const NOTARIZED_MESSAGE_LENGTH: int := 32

// This helper function describes a sequence of zeroes with the given length
ghost function SequenceOfZeroes(length: int) : (result: seq<byte>)
    requires length >= 0
    ensures  |result| == length
{
    seq(length, i => 0)
}

// This function specifies the legal initial states for the service,
// as a function of the size of the memory region, the space that the
// implementation requires not including the key, and whether the
// memory region is impervious to corruption. The initial state is
// allowed to be `None` only under specific conditions, e.g., if a
// memory region is provided with insufficient space.
//
ghost predicate SetupCorrect(optionalState: Option<NotaryServerState>, regionSize: int,
                             spaceNeededNotIncludingKey: int, imperviousToCorruption: bool)
{
    if optionalState.Some? then
        // If we return success from the initialization routine, we
        // must have set the counter to 0 and the last message to a
        // sequence of `NOTARIZED_MESSAGE_LENGTH` zero bytes.
        var state := optionalState.value;
        && ValidKeyView(state.key)
        && state.counter == 0
        && state.lastMessage == SequenceOfZeroes(NOTARIZED_MESSAGE_LENGTH)
    else
        // We're permitted to fail setup if there's a key pair that can't
        // be serialized in the space we have available in memory.
        || (exists keyView: KeyView, bytes: seq<byte> ::
            SpecKeyViewSerializationCorrect(keyView, bytes) && |bytes| + spaceNeededNotIncludingKey > regionSize)
        // We're permitted to fail setup if the memory experiences corruption
        || !imperviousToCorruption
}

// This function specifies the permitted behaviors of the service in
// response to a request to advance the counter and associate that new
// counter value with the given message. The inputs are:
//
// `state`: The abstract state before the operation
// `state'`: The abstract state after the operation
// `message`: The message in the request
// `imperviousToCorruption`: Whether the memory is impervious to corruption
// `success`: Whether the service indicates successful advance in its response
//
ghost predicate AdvanceCorrect(state: NotaryServerState, state': NotaryServerState, message: seq<byte>,
                               imperviousToCorruption: bool, success: bool)
{
    if success then
        // If we succeed, we must have incremented the counter and
        // updated the last message. Also, the message must be exactly
        // `NOTARIZED_MESSAGE_LENGTH` bytes long.
        && |message| == NOTARIZED_MESSAGE_LENGTH
        && state'.counter as int == state.counter as int + 1
        && state'.lastMessage == message
    else
        // If we fail, we must not change the state. There are three
        // conditions under which we're permitted to fail: (1) the
        // message supplied is the wrong length, (2) it would overflow
        // the counter, or (3) the memory exhibits evidence of
        // corruption.
        && state' == state
        && (
            || |message| != NOTARIZED_MESSAGE_LENGTH
            || state.counter == 0xFFFF_FFFF_FFFF_FFFF
            || !imperviousToCorruption
        )
}

// This function specifies the permitted behaviors of the service in
// response to a request to sign a message attesting to the linkage
// between the current counter and the last message notarized. The
// inputs are:
//
// `state`: The abstract state before (and after) the operation
// `signature`: The signature returned
//
ghost predicate SignCorrect(state: NotaryServerState, signature: seq<byte>)
{
    SpecSignCorrect(state.key.privateKey, SpecSerializeUint64(state.counter) + state.lastMessage, signature)
}

}
