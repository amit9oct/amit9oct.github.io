// var text = document.getElementById("about-me-latex").innerHTML;

// var generator = new latexjs.HtmlGenerator({ hyphenate: false });

// generator = latexjs.parse(text, { generator: generator });

// // document.head.appendChild(generator.stylesAndScripts("https://cdn.jsdelivr.net/npm/latex.js@0.12.4/dist/"))
// document.head.appendChild(generator.stylesAndScripts(""));
// var aboutMeDiv = document.getElementById("about-me");
// aboutMeDiv.innerHTML = "";
// aboutMeDiv.appendChild(generator.domFragment());

function readTextFile(file)
{
    var rawFile = new XMLHttpRequest();
    rawFile.open("GET", file, false);
    rawFile.onreadystatechange = function ()
    {
        if(rawFile.readyState === 4)
        {
            if(rawFile.status === 200 || rawFile.status == 0)
            {
                var allText = rawFile.responseText;
                var element = document.getElementById("about-me-latex");
                element.innerHTML = allText;
            }
        }
    }
}

import { LaTeXJSComponent } from "https://cdn.jsdelivr.net/npm/latex.js/dist/latex.mjs"
customElements.define("latex-js", LaTeXJSComponent);

