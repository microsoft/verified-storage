use std::{cell::RefCell, ptr::NonNull, rc::Rc};

#[derive(Debug)]
pub struct DoublyLinkedList<T> {
    head: Option<*mut DoublyLinkedListNode<T>>,
    tail: Option<*mut DoublyLinkedListNode<T>>,
    len: u64,
}

#[derive(Debug)]
pub struct DoublyLinkedListNode<T> {
    value: T,
    prev: Option<*mut DoublyLinkedListNode<T>>,
    next: Option<*mut DoublyLinkedListNode<T>>,
}

impl<T> DoublyLinkedListNode<T> {
    pub fn new(value: T) -> Self {
        Self {
            value,
            prev: None,
            next: None,
        }
    }

    pub fn get_value(&self) -> &T {
        &self.value
    }
}

impl<T> DoublyLinkedList<T> {
    pub fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    // the raw pointer stuff here is horrifying, but it seems like the easiest way
    // to do it with the cache map...

    pub fn push_front(
        &mut self,
        mut node: Box<DoublyLinkedListNode<T>>,
    ) -> *mut DoublyLinkedListNode<T> {
        node.prev = None;
        let node_ptr = if let Some(head_ptr) = self.head {
            node.next = Some(head_ptr);

            let head = unsafe { &mut *head_ptr };
            let node_ptr = Box::into_raw(node);
            head.prev = Some(node_ptr);
            self.head = Some(node_ptr);
            node_ptr
        } else {
            node.next = None;
            node.prev = None;

            let node_ptr = Box::into_raw(node);
            self.head = Some(node_ptr);
            self.tail = Some(node_ptr);
            node_ptr
        };
        self.len += 1;
        node_ptr
    }

    pub fn pop_back(&mut self) -> Option<Box<DoublyLinkedListNode<T>>> {
        if let Some(tail) = self.tail {
            Some(self.remove(tail))
        } else {
            None
        }
    }

    // NOTE: this will do weird things if you use a node that is
    // not in this list!
    pub fn remove(
        &mut self,
        node_ptr: *mut DoublyLinkedListNode<T>,
    ) -> Box<DoublyLinkedListNode<T>> {
        let mut node = unsafe { Box::from_raw(node_ptr) };
        let prev = node.prev;
        let next = node.next;
        node.next = None;
        node.prev = None;

        // next's prev becomes prev
        if let Some(next_ptr) = next {
            let next = unsafe { &mut *next_ptr };
            next.prev = prev;
        }

        if let Some(prev_ptr) = prev {
            let prev = unsafe { &mut *prev_ptr };
            prev.next = next;
        }

        // prev's next becomes next

        // if the node is the head or tail, update the list's fields accordingly
        if let Some(head) = self.head {
            if node_ptr == head {
                self.head = next;
            }
        }
        if let Some(tail) = self.tail {
            if node_ptr == tail {
                self.tail = prev;
            }
        }

        self.len -= 1;

        // return the now-owned boxed node
        node
    }
}
