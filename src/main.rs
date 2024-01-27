mod deriver;
mod parser;

#[macro_use]
extern crate rocket;
use rocket::fs::FileServer;

#[get("/parse?<query>")]
fn parse(query: &str) -> String {
    // deriver::derivation(query)
    match parser::parse_judgement(query) {
        Ok(s) => parser::htmlify(s),
        Err(e) => format!("<code>{e}</code>"),
    }
}

#[get("/derive?<query>")]
fn derive(query: &str) -> String {
    // format!("{}", deriver::derivation(query))
    let x = deriver::derivation_dot(query);
    println!("{x}");
    deriver::derivation_html(query)
}

#[launch]
fn rocket() -> _ {
    rocket::build()
        .mount("/", routes![parse, derive])
        .mount("/", FileServer::from("src/html/"))
}
