use itertools::Itertools;

/// Generate an ASCII figure of the given graph in DOT format.
///
/// This function depends on `Graph::Easy` being installed:
/// ```ignore
/// sudo cpan Graph::Easy
/// ```
/// Further information can be found
/// [here](https://stackoverflow.com/questions/3211801/graphviz-and-ascii-output).
pub fn graph_easy(dot: &str) -> std::io::Result<String> {
    use std::{io::Write, process::Stdio};

    let mut child = std::process::Command::new("graph-easy")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .args(["--from=dot", "--as=boxart"])
        .spawn()?;
    let mut stdin = child.stdin.take().unwrap();

    write!(stdin, "{dot}")?;
    drop(stdin);

    let output = child.wait_with_output()?;
    let result = String::from_utf8_lossy(&output.stdout);
    let leading_ws = result
        .lines()
        .filter(|l| !l.is_empty())
        .map(|l| l.find(|c: char| !c.is_whitespace()).unwrap_or(l.len()))
        .min()
        .unwrap_or(0);
    let result =
        result.lines().map(|l| if l.len() < leading_ws { l } else { &l[leading_ws..] }).join("\n");
    Ok(result)
}

/// Pipes the `dot` string generated into PNG into
/// [imgcat](https://iterm2.com/documentation-images.html)
///
/// `dot -T png | imgcat`
pub fn dot_imgcat(dot: &str) {
    use std::{
        io::Write,
        process::{Command, Stdio},
    };

    let dot_cmd = Command::new("dot")
        .args([
            "-Gmargin=0.7",
            "-Gbgcolor=#ffffff00",
            "-Gcolor=white",
            "-Gfontcolor=white",
            "-Gfontname=FiraCode NFM",
            "-Ncolor=white",
            "-Nfontcolor=white",
            "-Nfontname=FiraCode NFM",
            "-Ecolor=white",
            "-Efontcolor=white",
            "-Efontname=FiraCode NFM",
        ])
        .args(["-T", "png"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let imgcat = Command::new("imgcat")
        .stdin(Stdio::from(dot_cmd.stdout.unwrap()))
        .stdout(Stdio::inherit())
        .spawn()
        .unwrap();

    dot_cmd.stdin.unwrap().write_all(dot.as_bytes()).unwrap();

    imgcat.wait_with_output().unwrap();
}
