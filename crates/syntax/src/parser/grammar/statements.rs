use super::*;

pub fn stmt(p: &mut Parser) -> StatementParsed {
    if p.at(T![;]) {
        p.expect(T![;]);
        return StatementParsed::Statement;
    }

    match p.current() {
        T![let] => let_stmt(p),
        T![assume] => assume_stmt(p),
        T![assert] => assert_stmt(p),
        t if is_start_of_expr(t) => return expr_stmt(p),
        EOF => p.unexpected_eof(),
        _ => {
            if !item_opt(p) {
                p.error("expected a statement here");
                p.bump();
            }
        }
    }

    StatementParsed::Statement
}

pub fn expr_stmt(p: &mut Parser) -> StatementParsed {
    let expr_checkpoint = p.checkpoint();
    match expr(p, Location::NONE) {
        Some(bl) => StatementParsed::Expression(expr_checkpoint, bl),
        None => StatementParsed::Expression(expr_checkpoint, BlockLike::NotBolck),
    }
}

pub fn let_stmt(p: &mut Parser) {
    assert!(p.at(T![let]));

    p.start_node(LET_STMT, |p| {
        p.bump();

        if p.at(T![mut]) {
            p.bump();
        }

        name(p);

        if p.at(T![:]) {
            p.bump();
            ty(p);
        }

        if p.at(T![=]) {
            p.bump();
            expr(p, Location::NONE);
        }

        p.semicolon();
    });
}

pub fn assume_stmt(p: &mut Parser) {
    assert!(p.at(T![assume]));

    p.start_node(ASSUME_STMT, |p| {
        p.bump();

        comma_expr(p, Location::NONE);
        p.semicolon();
    });
}

pub fn assert_stmt(p: &mut Parser) {
    assert!(p.at(T![assert]));

    p.start_node(ASSERT_STMT, |p| {
        p.bump();

        comma_expr(p, Location::NONE);
        p.semicolon();
    });
}

pub fn block(p: &mut Parser) {
    if !p.at(T!['{']) {
        return;
    }
    p.start_node(BLOCK_EXPR, |p| {
        p.expect(T!['{']);

        let mut trailing = None;

        while !p.at(EOF) && !p.at(T!['}']) {
            if let Some((cp, block_like)) = trailing.take() {
                p.start_node_at(cp, EXPR_STMT, |p| {
                    if let BlockLike::NotBolck = block_like {
                        p.semicolon();
                    }
                });
                continue;
            }

            match stmt(p) {
                StatementParsed::Expression(next_cp, next_block_like) => {
                    trailing = Some((next_cp, next_block_like));
                }
                StatementParsed::Statement => {}
            }
        }

        p.expect(T!['}']);
    });
}
