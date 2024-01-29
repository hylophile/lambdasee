const result = document.querySelector("#parse-result");
const deriveResult = document.querySelector("#derive-result");
const graphResult = document.querySelector("#graph-result");
const width = graphResult.clientWidth;
const height = graphResult.clientHeight;
const queryInput = document.querySelector("#query");

result.addEventListener("htmx:afterSwap", () => {
  deriveResult.innerHTML = "";
  graphResult.innerHTML = "";
  Prism.highlightAll();
});

document.addEventListener("htmx:responseError", (e) => {
  e.detail.target.innerHTML = "TODO: server panic.";
});

deriveResult.addEventListener("htmx:afterSwap", () => {
  Prism.highlightAll();
});

graphResult.addEventListener("htmx:afterSwap", () => {
  scaleToFit();
});

queryInput.addEventListener("input", () => {
  window.location.replace(
    "#query=" + btoa(encodeURIComponent(queryInput.innerText)),
  );
});

window.addEventListener("load", () => {
  const hashValue = window.location.hash.substring(1);
  const encodedValue = hashValue.split("=")[1];

  if (encodedValue) {
    queryInput.innerText = decodeURIComponent(atob(encodedValue));
    queryInput.dispatchEvent(new Event("input"));
  }
});

window.normalize = (s) => s.replaceAll("\u{a0}", " ");

const scaleToFit = () => {
  const svg = SVG(document.querySelector("svg"))
    .panZoom({ zoomFactor: 0.2 })
    .size(width - 200, 1000);
  // .viewbox(
  //                        `0 0 ${graphResult.clientWidth} ${graphResult.clientHeight}`,
  //                    );
  window.svg = svg;

  graphResult.scrollIntoView({
    behavior: "smooth",
    block: "start",
    inline: "nearest",
  });
};
