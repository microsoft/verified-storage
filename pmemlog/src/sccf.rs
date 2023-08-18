/*
  Simple crash-consistency framework (open source)
*/

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

    pub open spec fn is_state_allowable<AbstractStorage, AbstractService>(
        pre_operation_abstract_state: AbstractService,
        crash_state: AbstractStorage,
        recovery_view: FnSpec(AbstractStorage) -> Option<AbstractService>,
        abstract_next: FnSpec(AbstractService, AbstractService) -> bool
        ) -> bool
    {
        let crash_abstract_state = recovery_view(crash_state);
        ||| crash_abstract_state == Some(pre_operation_abstract_state)
        ||| {
                &&& crash_abstract_state.is_Some()
                &&& abstract_next(pre_operation_abstract_state, crash_abstract_state.unwrap())
           }
    }

    pub trait CheckPermission<AbstractStorage>
    {
        spec fn check_permission(&self, state: AbstractStorage) -> bool;
    }

}
