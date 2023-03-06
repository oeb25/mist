struct List {
    next: List?,
    elem: Int,
    ghost content: Seq[Int],
}

invariant List {
    if this.next == null { this.content = Seq[Int]() }
    if this.next != null { this.content == Seq(this.elem) ++ this.next.content }
}

fn create() -> List
    ensures result.content == Seq[Int]()
{
    return List { content: Seq[Int]() }
}
