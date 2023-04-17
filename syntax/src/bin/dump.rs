use color_eyre::eyre::ContextCompat;

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    let src = std::fs::read_to_string(
        std::env::args()
            .nth(1)
            .wrap_err("missing file as first argument")?,
    )?;
    let (doc, _errors) = mist_syntax::parse(&src);
    eprintln!("{:#?}", doc.syntax());
    Ok(())
}
