mod deriver;
mod expr;
mod parser;

#[macro_use]
extern crate rocket;
use std::io::{Read, Write};
use std::process::{Command, Stdio};

use rocket::fs::FileServer;

#[get("/parse?<query>")]
fn parse(query: &str) -> String {
    // deriver::derivation(query)
    match parser::parse_judgement(query) {
        Ok(s) => expr::htmlify(&s),
        Err(e) => format!("<code>{e}</code>"),
    }
}

#[get("/derive?<query>")]
fn derive(query: &str) -> String {
    let d = deriver::derivation(query);
    deriver::derivation_html(&d)
}

#[get("/graph?<query>")]
fn graph(query: &str) -> String {
    let d = deriver::derivation(query);
    let dot = deriver::derivation_dot(&d);
    // println!("{dot}");
    let svg = run(dot);
    svg
}

#[launch]
fn rocket() -> _ {
    rocket::build()
        .mount("/", routes![parse, derive, graph])
        .mount("/", FileServer::from("src/html/"))
}

pub fn run(code: String) -> String {
    let mut child = Command::new("dot")
        .stdin(Stdio::piped())
        .stderr(Stdio::piped())
        .stdout(Stdio::piped())
        .arg("-Tsvg:cairo")
        .spawn()
        .expect("Failed to spawn child process");

    let mut stdin = child.stdin.take().expect("Failed to open stdin");
    std::thread::spawn(move || {
        stdin
            .write_all(code.as_bytes())
            .expect("Failed to write to stdin");
    });

    let output = child.wait_with_output().expect("Failed to read stdout");
    String::from_utf8_lossy(&output.stdout).to_string()
}
