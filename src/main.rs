mod deriver;
mod parser;

#[macro_use]
extern crate rocket;
use rocket::fs::FileServer;

#[get("/parse?<query>")]
fn parse(query: &str) -> String {
    match parser::parse_judgement(query) {
        Ok(s) => {
            format!("{}", parser::stringify(s))
        }
        Err(e) => format!("<span class='error'>Error!</span><pre>{:?}</pre>", e),
    }
}

#[launch]
fn rocket() -> _ {
    rocket::build()
        .mount("/", routes![parse])
        .mount("/", FileServer::from("src/html/"))
}
