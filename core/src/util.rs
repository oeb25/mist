#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Position {
    pub line: u32,
    pub character: u32,
}

impl Position {
    pub fn new(line: u32, character: u32) -> Self {
        Self { line, character }
    }
    pub fn to_byte_offset(self, src: &str) -> Option<usize> {
        let mut lines = self.line;
        let mut columns = self.character;
        src.char_indices()
            .find(|&(_, c)| {
                if lines == 0 {
                    if columns == 0 {
                        return true;
                    } else {
                        columns -= 1
                    }
                } else if c == '\n' {
                    lines -= 1;
                }
                false
            })
            .map(|(idx, _)| idx)
    }
    pub fn from_byte_offset(src: &str, byte_offset: usize) -> Self {
        if src[0..byte_offset].is_empty() {
            return Position::new(0, 0);
        }

        if src[0..byte_offset].ends_with('\n') {
            let l = src[0..byte_offset].lines().count();
            Position::new(l as _, 0)
        } else {
            let l = src[0..byte_offset].lines().count() - 1;
            let c = src[0..byte_offset].lines().last().unwrap().len();
            Position::new(l as _, c as _)
        }
    }
}

impl std::fmt::Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.character)
    }
}
