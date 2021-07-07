use thiserror::Error;

#[derive(Debug, PartialEq, Eq, Error)]
#[error("call stack capacity exceeded, pushing of address {address_not_pushed:X} failed")]
pub struct CallStackCapacityExceededError {
    pub address_not_pushed: u16,
}

#[derive(Debug, PartialEq, Eq)]
pub struct CallStack(Vec<u16>);

impl CallStack {
    pub fn with_capacity(capacity: usize) -> Self {
        Self(Vec::with_capacity(capacity))
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn pop(&mut self) -> Option<u16> {
        self.0.pop()
    }

    pub fn push(&mut self, address: u16) -> Result<(), CallStackCapacityExceededError> {
        if self.0.len() < self.0.capacity() {
            self.0.push(address);
            Ok(())
        } else {
            Err(CallStackCapacityExceededError {
                address_not_pushed: address,
            })
        }
    }
}

impl From<Vec<u16>> for CallStack {
    fn from(vec: Vec<u16>) -> Self {
        Self(vec)
    }
}

impl Default for CallStack {
    fn default() -> Self {
        Self::with_capacity(128)
    }
}
