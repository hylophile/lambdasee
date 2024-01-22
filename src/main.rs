mod deriver;
mod parser;

#[macro_use]
extern crate rocket;
use rocket::fs::FileServer;

#[get("/parse?<query>")]
fn parse(query: &str) -> String {
    // deriver::derivation(query)
    match parser::parse_judgement(query) {
        Ok(s) => {
            format!("{}", parser::stringify(s))
        }
        Err(e) => format!("{}", e),
    }
}

#[get("/derive?<query>")]
fn derive(query: &str) -> String {
    format!("\n{}", deriver::derivation(query))
}

#[launch]
fn rocket() -> _ {
    rocket::build()
        .mount("/", routes![parse, derive])
        .mount("/", FileServer::from("src/html/"))
}
