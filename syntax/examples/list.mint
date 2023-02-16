struct List {
    next: List?,
    elem: Int,
}

fn head(this: &mut List) -> Int {
    return this.elem;
}

fn append(this: &mut List, e: Int) {
    if this.next == null {
        let n = List {
            next: null,
        };
        this.elem = e;
        this.next = n;
    } else {
        append(&mut this.next, e);
    }
}

fn prepend(this: List, e: Int) -> List {
    return List { next: this, elem: e };
}

fn create() -> List {
    return List {};
}

fn concat(this: &mut List, that: List) {
    if this.next == null {
        this.next = that.next;
        this.elem = that.elem;
    } else {
        concat(&mut this.next, that);
    }
}

fn reverse(this: List) -> List {
    return reverse_helper(this, null);
}

fn reverse_helper(this: List, last: List?) -> List {
    if this.next == null {
        if last == null {
            return this;
        } else {
            return last;
        }
    } else {
        let n = this.next;
        return reverse_helper(n, this);
    }
}
