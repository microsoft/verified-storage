use std::{cell::RefCell, ptr::NonNull, rc::Rc};

#[derive(Debug)]
pub struct DoublyLinkedList<T> {
    list_vec: Vec<Option<DoublyLinkedListNode<T>>>,
    free_list: Vec<usize>,
    head: Option<usize>,
    tail: Option<usize>,
    len: u64,
}

#[derive(Debug, Clone)]
pub struct DoublyLinkedListNode<T> {
    value: Box<T>,
    prev: Option<usize>,
    next: Option<usize>,
}

impl<T> DoublyLinkedListNode<T> {
    pub fn new(value: Box<T>) -> Self {
        Self {
            value,
            prev: None,
            next: None,
        }
    }

    pub fn get_value(&self) -> &T {
        &self.value
    }

    pub fn take_value(self) -> Box<T> {
        self.value
    }
}

impl<T> DoublyLinkedList<T> {
    pub fn new(capacity: usize) -> Self {
        Self {
            list_vec: (0..capacity).map(|_| None).collect(),
            free_list: Vec::from_iter(0..capacity),
            head: None,
            tail: None,
            len: 0,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn capacity(&self) -> usize {
        self.list_vec.len()
    }

    pub fn len(&self) -> u64 {
        self.len
    }

    pub fn peek_head(&self) -> Option<&T> {
        if let Some(head_index) = self.head {
            let head = self.list_vec.get(head_index).unwrap();
            if let Some(head) = head {
                Some(head.get_value())
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn push_front(&mut self, value: Box<T>) -> Option<usize> {
        let mut node = DoublyLinkedListNode {
            value,
            prev: None,
            next: None,
        };

        let new_index = self.free_list.pop()?;
        if let Some(head_index) = self.head {
            node.next = Some(head_index);
            let head = self.list_vec.get_mut(head_index).unwrap().as_mut().unwrap();
            head.prev = Some(new_index);
            self.head = Some(new_index);
        } else {
            node.next = None;
            self.head = Some(new_index);
            self.tail = Some(new_index);
        };
        self.list_vec[new_index] = Some(node);
        self.len += 1;
        Some(new_index)
    }

    pub fn pop_back(&mut self) -> Option<Box<T>> {
        if let Some(tail) = self.tail {
            self.remove(tail)
        } else {
            None
        }
    }

    pub fn remove(&mut self, node_index: usize) -> Option<Box<T>> {
        let mut node: DoublyLinkedListNode<T> = self.list_vec.get_mut(node_index)?.take()?;
        let prev_index = node.prev;
        let next_index = node.next;
        node.next = None;
        node.prev = None;

        self.free_list.push(node_index);

        // next's prev becomes prev
        if let Some(next_index) = next_index {
            let next_node = self.list_vec.get_mut(next_index).unwrap().as_mut().unwrap();
            next_node.prev = prev_index;
        }

        // prev's next becomes next
        if let Some(prev_index) = prev_index {
            let prev_node = self.list_vec.get_mut(prev_index).unwrap().as_mut().unwrap();

            prev_node.next = next_index;
        }

        // if the node being removed was head and/or tail, update those fields
        if let Some(head) = self.head {
            if node_index == head {
                self.head = next_index;
            }
        }
        if let Some(tail) = self.tail {
            if node_index == tail {
                self.tail = prev_index;
            }
        }

        self.len -= 1;

        Some(node.take_value())
    }
}
