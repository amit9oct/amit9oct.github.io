// var text = document.getElementById("about-me-latex").innerHTML;

// var generator = new latexjs.HtmlGenerator({ hyphenate: false });

// generator = latexjs.parse(text, { generator: generator });

// // document.head.appendChild(generator.stylesAndScripts("https://cdn.jsdelivr.net/npm/latex.js@0.12.4/dist/"))
// document.head.appendChild(generator.stylesAndScripts(""));
// var aboutMeDiv = document.getElementById("about-me");
// aboutMeDiv.innerHTML = "";
// aboutMeDiv.appendChild(generator.domFragment());

import { LaTeXJSComponent } from "https://cdn.jsdelivr.net/npm/latex.js/dist/latex.mjs"
customElements.define("latex-js", LaTeXJSComponent)