/*
  Simple crash-consistency framework (open source)
*/

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

    pub open spec fn is_state_allowable<AbstractStorage, AbstractService>(
        pre_operation_state: AbstractStorage,
        crash_state: AbstractStorage,
        recovery_view: spec_fn(AbstractStorage) -> Option<AbstractService>,
        abstract_next: spec_fn(AbstractService, AbstractService) -> bool
        ) -> bool
    {
        let pre_operation_abstract_state = recovery_view(pre_operation_state);
        let crash_abstract_state = recovery_view(crash_state);
        ||| crash_abstract_state == pre_operation_abstract_state
        ||| {
                &&& pre_operation_abstract_state is Some
                &&& crash_abstract_state is Some
                &&& abstract_next(pre_operation_abstract_state.unwrap(), crash_abstract_state.unwrap())
            }
    }

    pub trait CheckPermission<AbstractStorage>
    {
        spec fn check_permission(&self, state: AbstractStorage) -> bool;
    }

}
