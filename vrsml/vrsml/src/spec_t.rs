use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use deps_hack::pmcopy_primitive;
use deps_hack::rand;
use deps_hack::{RandomizedSigner, RsaPrivateKey, Sha256, Signature, SignatureEncoding, SigningKey, VerifyingKey};
use vstd::pcm::*;
use vstd::invariant::*;

verus! {

    pub trait ApplicationStateMachineSpec {
        spec fn guid() -> u128;
        spec fn initialize_state(init_params: Seq<u8>) -> Seq<u8>;
        spec fn handle_request(state: Seq<u8>, request: Seq<u8>) -> (Seq<u8>, Seq<u8>);
    }

    pub trait ApplicationStateMachineImpl: View<V = Seq<u8>> + Sized {
        type MySpec: ApplicationStateMachineSpec;

        spec fn valid(&self) -> bool;

        exec fn initialize_state(init_params: &[u8]) -> (state: Self)
            ensures
                Self::MySpec::initialize_state(init_params@) == state@,
                state.valid(),
        ;

        exec fn handle_request(&mut self, request: &[u8]) -> (response: Vec<u8>)
            requires
                old(self).valid(),
            ensures
                Self::MySpec::handle_request(old(self)@, request@) == (self@, response@),
                self.valid(),
            ;
    }

    #[verifier::external_body]
    pub struct RsaPrivateKeyWrapper
    {
        pub private_key: SigningKey<Sha256>,
    }

    impl View for RsaPrivateKeyWrapper
    {
        type V = Seq<u8>;
        uninterp spec fn view(&self) -> Seq<u8>; // gives public key
    }

    impl RsaPrivateKeyWrapper
    {
        #[verifier::external_body]
        pub fn sign(&self, message: &[u8]) -> (signature: Box<[u8]>)
            ensures
                is_valid_signature(signature@, self@, message@),
        {
            let mut rng = rand::thread_rng();
            let signature = self.private_key.sign_with_rng(&mut rng, message).to_bytes();
            signature
        }
    }

    #[verifier::external_body]
    pub struct RsaPublicKeyWrapper
    {
        pub public_key: VerifyingKey<Sha256>,
    }

    impl View for RsaPublicKeyWrapper
    {
        type V = Seq<u8>;
        uninterp spec fn view(&self) -> Seq<u8>;
    }

    pub uninterp spec fn is_valid_signature(signature: Seq<u8>, public_key: Seq<u8>, message: Seq<u8>) -> bool;

    pub open spec fn is_formatted_request(s: Seq<u8>, request: Seq<u8>) -> bool
    {    
        &&& request.len() <= u64::MAX
        &&& s == 0u64.spec_to_bytes() + (request.len() as u64).spec_to_bytes() + request
    }

    pub open spec fn is_formatted_response(s: Seq<u8>, response: Seq<u8>, request_number: int) -> bool
    {
        &&& response.len() <= u64::MAX
        &&& 0 <= request_number <= u64::MAX
        &&& s == 1u64.spec_to_bytes() + (request_number as u64).spec_to_bytes() +
                 (response.len() as u64).spec_to_bytes() + response
    }

    #[verifier::ext_equal]
    pub struct AbstractSystemStateConstants<S: ApplicationStateMachineSpec>
    {
        pub init_params: Seq<u8>,
        pub client_public_key: Seq<u8>,
        pub server_public_key: Seq<u8>,
        pub state_machine: Ghost<Option<S>>,
    }

    #[verifier::ext_equal]
    pub struct AbstractSystemState<S: ApplicationStateMachineSpec>
    {
        pub c: AbstractSystemStateConstants<S>,
        pub client_messages: Set<Seq<u8>>,
        pub server_messages: Set<Seq<u8>>,
        pub ordered_requests: Seq<Seq<u8>>,
    }

    #[verifier::ext_equal]
    pub enum AbstractSystemStep
    {
        Stutter,
        ReceiveClientMessage{ client_message: Seq<u8> },
        ExecuteRequest{ client_message: Seq<u8>, server_message: Seq<u8>, request: Seq<u8>, response: Seq<u8> },
        SendInternalMessage{ server_message: Seq<u8> },
    }

    impl<S: ApplicationStateMachineSpec> AbstractSystemState<S>
    {
        pub open spec fn get_nth_state(self, n: int) -> Seq<u8>
            recommends
                0 <= n <= self.ordered_requests.len(),
            decreases n
        {
            if n <= 0 {
                S::initialize_state(self.c.init_params)
            }
            else {
                S::handle_request(self.get_nth_state(n - 1), self.ordered_requests[n - 1]).0
            }
        }

        pub open spec fn get_response_to_nth_request(self, n: int) -> Seq<u8>
            recommends
                0 <= n < self.ordered_requests.len(),
        {
            S::handle_request(self.get_nth_state(n), self.ordered_requests[n]).1
        }

        pub open spec fn get_current_state(self) -> Seq<u8>
        {
            self.get_nth_state(self.ordered_requests.len() as int)
        }

        pub open spec fn update_with_received_client_message(self, client_message: Seq<u8>) -> Self
        {
            Self{ client_messages: self.client_messages.insert(client_message), ..self }
        }

        pub open spec fn update_with_authorized_server_message(self, server_message: Seq<u8>) -> Self
        {
            Self{ server_messages: self.server_messages.insert(server_message), ..self }
        }

        pub open spec fn next_receive_client_message(self, other: Self, client_message: Seq<u8>) -> bool
        {
            other == self.update_with_received_client_message(client_message)
        }

        pub open spec fn next_execute_request(
            self,
            other: Self,
            client_message: Seq<u8>,
            server_message: Seq<u8>,
            request: Seq<u8>,
            response: Seq<u8>
        ) -> bool
        {
            &&& self.client_messages.contains(client_message)
            &&& is_formatted_request(client_message, request)
            &&& is_formatted_response(server_message, response, self.ordered_requests.len() as int)
            &&& response == S::handle_request(self.get_current_state(), request).1
            &&& other == Self{ ordered_requests: self.ordered_requests.push(request),
                              server_messages: self.server_messages.insert(server_message),
                              ..self }
        }

        pub open spec fn next_send_internal_message(self, other: Self, server_message: Seq<u8>) -> bool
        {
            // An internal message must not be misinterpretable as a response
            &&& forall|response, request_number| !is_formatted_response(server_message, response, request_number)
            &&& other == Self{ server_messages: self.server_messages.insert(server_message), ..self }
        }

        pub open spec fn next_step(self, other: Self, step: AbstractSystemStep) -> bool
        {
            match step
            {
                AbstractSystemStep::Stutter =>
                    self == other,
                AbstractSystemStep::ReceiveClientMessage{ client_message } =>
                    self.next_receive_client_message(other, client_message),
                AbstractSystemStep::ExecuteRequest{ client_message, server_message, request, response } =>
                    self.next_execute_request(other, client_message, server_message, request, response),
                AbstractSystemStep::SendInternalMessage{ server_message } =>
                    self.next_send_internal_message(other, server_message),
            }
        }

        pub open spec fn next(self, other: Self) -> bool
        {
            exists |step: AbstractSystemStep| self.next_step(other, step)
        }
    }

    #[verifier::reject_recursive_types(S)]
    #[verifier::ext_equal]
    pub struct AbstractSystemStateKnowledge<S: ApplicationStateMachineSpec>
    {
        pub k: spec_fn(AbstractSystemState<S>) -> bool
    }

    impl <S: ApplicationStateMachineSpec> AbstractSystemStateKnowledge<S>
    {
        pub open spec fn contains(self, s: AbstractSystemState<S>) -> bool
        {
            &&& self.closed_under_next()
            &&& (self.k)(s)
        }

        pub open spec fn closed_under_next(self) -> bool
        {            
            forall|s1, s2| (self.k)(s1) && s1.next(s2) ==> (self.k)(s2)
        }

        pub open spec fn update_with_received_client_message(self, client_message: Seq<u8>) -> Self
        {
            Self { k: |s: AbstractSystemState<S>| s.client_messages.contains(client_message) && (self.k)(s) }
        }

        pub open spec fn update_with_authorized_server_message(self, server_message: Seq<u8>) -> Self
        {
            Self { k: |s: AbstractSystemState<S>| s.server_messages.contains(server_message) && (self.k)(s) }
        }

        pub open spec fn update_with_ordered_request(self, request: Seq<u8>, request_number: int) -> Self
        {
            Self { k: |s: AbstractSystemState<S>| {
                       &&& s.ordered_requests.len() > request_number
                       &&& s.ordered_requests[request_number] == request
                       &&& (self.k)(s)
                   } }
        }
    }

    pub trait AbstractSystemStateProtocol<S: ApplicationStateMachineSpec>
    {
        spec fn permits(state: AbstractSystemState<S>) -> bool;

        proof fn lemma_permits_empty_state()
            ensures
                forall|s: AbstractSystemState<S>|
                    s.client_messages.is_empty() && s.server_messages.is_empty() && s.ordered_requests.len() == 0 ==>
                    #[trigger] Self::permits(s)
            ;

        proof fn lemma_allows_arbitrary_client_messages()
            ensures
                forall|s: AbstractSystemState<S>, client_message: Seq<u8>|
                    Self::permits(s) ==> Self::permits(#[trigger] s.update_with_received_client_message(client_message))
            ;
    }

    pub open spec fn update_permitted<S: ApplicationStateMachineSpec, P: AbstractSystemStateProtocol<S>>(
        k_current: AbstractSystemStateKnowledge<S>,
        k_next: AbstractSystemStateKnowledge<S>,
        state_updater: spec_fn(AbstractSystemState<S>) -> AbstractSystemState<S>
    ) -> bool
    {
        &&& k_next.closed_under_next()
        &&& forall|s| k_current.contains(s) && P::permits(s) ==>
                s.next(state_updater(s)) && k_next.contains(state_updater(s)) && P::permits(state_updater(s))
    }

    impl<S: ApplicationStateMachineSpec> PCM for AbstractSystemStateKnowledge<S>
    {
        open spec fn valid(self) -> bool
        {
            true
        }

        open spec fn op(self, other: Self) -> Self
        {
            Self{ k: |s| (self.k)(s) && (other.k)(s) }
        }

        open spec fn unit() -> Self
        {
            Self { k: |s| true }
        }

        proof fn closed_under_incl(a: Self, b: Self) { }
        proof fn commutative(a: Self, b: Self) { }
        proof fn associative(a: Self, b: Self, c: Self) { }
        proof fn op_unit(a: Self) { }
        proof fn unit_valid() { }
    }

    #[verifier::ext_equal]
    pub struct TrustedStateMachine<S: ApplicationStateMachineSpec, P: AbstractSystemStateProtocol<S>>
    {
        c: AbstractSystemStateConstants<S>,
        knowledge_loc: Loc,
        client_public_key: RsaPublicKeyWrapper,
        server_private_key: RsaPrivateKeyWrapper,
        _application_spec: Ghost<Option<S>>,
        _protocol: Ghost<Option<P>>,
    }


    impl<S: ApplicationStateMachineSpec, P: AbstractSystemStateProtocol<S>> TrustedStateMachine<S, P>
    {
        pub closed spec fn spec_client_public_key(&self) -> Seq<u8>
        {
            self.client_public_key@
        }

        pub closed spec fn spec_server_public_key(&self) -> Seq<u8>
        {
            self.server_private_key.view()
        }

        pub closed spec fn spec_knowledge_loc(&self) -> Loc
        {
            self.knowledge_loc
        }

        #[verifier::external_body]
        pub proof fn receive_client_message(
            &self,
            client_message: Seq<u8>,
            client_signature: Seq<u8>,
            tracked old_knowledge: Resource<AbstractSystemStateKnowledge<S>>,
        ) -> (tracked new_knowledge: Resource<AbstractSystemStateKnowledge<S>>)
            requires
                is_valid_signature(client_signature, self.spec_client_public_key(), client_message),
                old_knowledge.loc() == self.spec_knowledge_loc(),
            ensures
                new_knowledge.loc() == old_knowledge.loc(),
                new_knowledge.value() == old_knowledge.value().update_with_received_client_message(client_message)
        {
            arbitrary()
        }

        #[verifier::external_body]
        pub proof fn receive_server_message(
            &self,
            server_message: Seq<u8>,
            server_signature: Seq<u8>,
            tracked old_knowledge: Resource<AbstractSystemStateKnowledge<S>>,
        ) -> (tracked new_knowledge: Resource<AbstractSystemStateKnowledge<S>>)
            requires
                is_valid_signature(server_signature, self.spec_server_public_key(), server_message),
                old_knowledge.loc() == self.spec_knowledge_loc(),
            ensures
                new_knowledge.loc() == old_knowledge.loc(),
                new_knowledge.value() == old_knowledge.value().update_with_authorized_server_message(server_message)
        {
            arbitrary()
        }

        #[verifier::external_body]
        pub proof fn order_request(
            &self,
            client_message: Seq<u8>,
            request: Seq<u8>,
            request_number: int,
            tracked old_knowledge: Resource<AbstractSystemStateKnowledge<S>>,
        ) -> (tracked new_knowledge: Resource<AbstractSystemStateKnowledge<S>>)
            requires
                old_knowledge.loc() == self.spec_knowledge_loc(),
                forall|s: AbstractSystemState<S>| #[trigger] old_knowledge.value().contains(s) && P::permits(s) ==>
                    s.client_messages.contains(client_message),
                is_formatted_request(client_message, request),
                0 <= request_number,
                forall|s: AbstractSystemState<S>| {
                    &&& #[trigger] old_knowledge.value().contains(s)
                    &&& P::permits(s)
                    &&& s.ordered_requests.len() > request_number
                } ==> s.ordered_requests[request_number] == request,
            ensures
                new_knowledge.loc() == old_knowledge.loc(),
                new_knowledge.value() == old_knowledge.value().update_with_ordered_request(request, request_number),
        {
            arbitrary()
        }

        #[verifier::external_body]
        pub proof fn authorize_sending_response(
            &self,
            response: Seq<u8>,
            request_number: int,
            formatted_response: Seq<u8>,
            tracked old_knowledge: Resource<AbstractSystemStateKnowledge<S>>,
        ) -> (tracked new_knowledge: Resource<AbstractSystemStateKnowledge<S>>)
            requires
                old_knowledge.loc() == self.spec_knowledge_loc(),
                forall|s: AbstractSystemState<S>| #[trigger] old_knowledge.value().contains(s) && P::permits(s) ==> {
                    &&& 0 <= request_number < s.ordered_requests.len()
                    &&& s.get_response_to_nth_request(request_number) == response
                    &&& P::permits(s.update_with_authorized_server_message(formatted_response))
                },
                is_formatted_response(formatted_response, response, request_number),
            ensures
                new_knowledge.loc() == self.spec_knowledge_loc(),
                new_knowledge.value() ==
                    old_knowledge.value().update_with_authorized_server_message(formatted_response),
        {
            arbitrary()
        }

        #[verifier::external_body]
        pub proof fn authorize_sending_internal_message(
            &self,
            server_message: Seq<u8>,
            tracked old_knowledge: Resource<AbstractSystemStateKnowledge<S>>,
        ) -> (tracked new_knowledge: Resource<AbstractSystemStateKnowledge<S>>)
            requires
                old_knowledge.loc() == self.spec_knowledge_loc(),
                forall|s: AbstractSystemState<S>| #[trigger] old_knowledge.value().contains(s) && P::permits(s) ==>
                    P::permits(s.update_with_authorized_server_message(server_message)),
                forall|response: Seq<u8>, request_number: int|
                    !is_formatted_response(server_message, response, request_number),
            ensures
                new_knowledge.loc() == self.spec_knowledge_loc(),
                new_knowledge.value() ==
                    old_knowledge.value().update_with_authorized_server_message(server_message),
        {
            arbitrary()
        }

        #[verifier::external_body]
        pub exec fn send_authorized_server_message(
            &self,
            server_message: &[u8],
            tracked knowledge: &Resource<AbstractSystemStateKnowledge<S>>,
        ) -> (message_signature: Box<[u8]>)
            requires
                knowledge.loc() == self.spec_knowledge_loc(),
                forall|s: AbstractSystemState<S>| #[trigger] knowledge.value().contains(s) && P::permits(s) ==>
                    s.server_messages.contains(server_message@),
            ensures
                is_valid_signature(message_signature@, self.spec_server_public_key(), server_message@),
        {
            self.server_private_key.sign(server_message)
        }
    }

}
