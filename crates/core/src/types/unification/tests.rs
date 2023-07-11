use std::fmt;

use crate::{testing::*, tests::fixture};

fn check_type_at(src: impl fmt::Display, f: impl FnOnce(String)) {
    let (db, fixture) = fixture(src);
    let m = fixture.marker(0);
    f(fixture.type_at(&db, m).display(&db).to_string())
}

#[test]
fn unification_instantiate_adt() {
    check_type_at(
        r#"
pure struct Bst {
    nodes: [Node],
}

pure struct Node {
    left: int,
    right: int,
    elem: int,
}

invariant Bst {
    forall n in 0..self.$0nodes.len {
        self.nodes[n].left < self.nodes.len &&
        self.nodes[n].right < self.nodes.len
    }
}
"#,
        expect!(@"ghost [Node]"),
    );
}
