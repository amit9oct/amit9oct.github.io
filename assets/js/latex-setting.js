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

function setSrc(url)
{
    var ele = document.getElementById("pdf-frame");
    ele.src = url;
    ele.style.width = '900px';
    ele.style.height = '900px';
    ele.style.cursor = 'hand';
    ele.innerHTML = `Pdf plugin unsupported for this browser click <a href='${url}'>here</a> to see the PDF.`;    
}

function setSrcDoc(data)
{
    var ele = document.getElementById("pdf-frame");
    ele.srcdoc = data;
    ele.style.width = '900px';
    ele.style.height = '900px';
    ele.style.cursor = 'hand';        
}

function checkIfLoaded()
{
    var ele = document.getElementById("pdf-frame");
    return ele.srcdoc !== "<p>Loading PDF ...</p>";
}

function progress_update_callback()
{
    var cnt = 0;
    return function(e){
        setSrcDoc("<p>Loading PDF " + ".".repeat(cnt%53) +"</p>");
        cnt += 1;
    };
}

function get_post_ajax(onSuccessCallback, onEmptyCallback, progressCallback, url)
{
    var xhttp = new XMLHttpRequest();
    xhttp.onprogress = progressCallback;
    xhttp.addEventListener("load", onEmptyCallback, false);
    xhttp.addEventListener("error", onEmptyCallback, false);
    xhttp.addEventListener("abort", onEmptyCallback, false);	  	
    xhttp.onreadystatechange = function()
    {
        if (xhttp.readyState == 4 && xhttp.status == 200)
        {
            onSuccessCallback(xhttp.responseText);
        }
        else if(xhttp.readyState == 4 && xhttp.status == 204)
        {
            onEmptyCallback(xhttp.responseText);
        }
    };
    xhttp.open("GET", url, true);
    xhttp.send();
}

function loadGooglePdfViewer(relUrl, maxRetryCount)
{
    if(checkIfLoaded())
    {
        return;
    }
    var assetUrl = `https://amit9oct.github.io${relUrl}`;
    var googleUrl = `https://docs.google.com/gview?embedded=true&url=${assetUrl}`;
    var successCallback = function(response)
    {
        setSrcDoc(response);
    };
    var emptyCallback = function(response) 
    {
        if(maxRetryCount >= 1) 
        {
            loadGooglePdfViewer(relUrl, maxRetryCount - 1);
        }
        else
        {
            setSrc(relUrl);
        }
    };
    get_post_ajax(successCallback, emptyCallback, progress_update_callback(), googleUrl);
}

var el = document.getElementById('pdf-load'); 
if (el) 
{ 
    var x = '/assets/resume/PublicResume.pdf';
    el.addEventListener('onload', 
    function()
    {
        loadGooglePdfViewer(x, 5);
    });
    loadGooglePdfViewer(x, 5);    
}

// import { LaTeXJSComponent } from "https://cdn.jsdelivr.net/npm/latex.js/dist/latex.mjs"
// customElements.define("latex-js", LaTeXJSComponent);

