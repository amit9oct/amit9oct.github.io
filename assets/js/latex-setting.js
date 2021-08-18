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

//not used
function loadPDF(relUrl)
{
    var url = `https://amit9oct.github.io${relUrl}`;

    // Loaded via <script> tag, create shortcut to access PDF.js exports.
    var pdfjsLib = window['pdfjs-dist/build/pdf'];
    
    // The workerSrc property shall be specified.
    pdfjsLib.GlobalWorkerOptions.workerSrc = '/assets/js/pdf.worker.js';
    
    var currPage = 1; //Pages are 1-based not 0-based
    var numPages = 0;
    var thePDF = null;

    function handlePages(page)
    {
        //This gives us the page's dimensions at full scale
        var viewport = page.getViewport( {scale: 2} );
        var pdfStatus = document.getElementById("pdf-load-status");
        var pdfDiv = document.getElementById("pdf-canvas");
        var pdfTextDiv = document.getElementById("pdf-text");
        var pos = getPos(pdfDiv);
        pdfTextDiv.style.left = pos.offsetLeft + 'px';
        pdfTextDiv.style.top = pos.offsetTop + 'px';
        pdfTextDiv.style.position = "absolute";
    
        //We'll create a canvas for each page to draw it on
        var canvas = document.createElement("canvas");
        canvas.id = `pdf-canvas${currPage}`;
        canvas.style.display = "block";
        var context = canvas.getContext('2d');
    
        canvas.height = viewport.height;
        canvas.width = viewport.width;
    
        //Draw it on the canvas
        page.render({canvasContext: context, viewport: viewport})
            .promise.then(function() 
            {
                // Returns a promise, on resolving it will return text contents of the page
                return page.getTextContent();
            }).then(function(textContent) 
            {
                //Add it to the web page
                pdfDiv.appendChild(canvas);
                var line = document.createElement("hr");
                pdfDiv.appendChild(line);                
                // Assign CSS to the textLayer element
                var textLayer = document.createElement("div");
                textLayer.id = `textLayer${currPage}`;
                // Pass the data to the method for rendering of text over the pdf canvas.
                pdfjsLib.renderTextLayer({
                    textContent: textContent,
                    container: textLayer,
                    viewport: viewport,
                    textDivs: []
                });                
                textLayer.style.left = `${(pos.offsetLeft + canvas.offsetLeft)}px`;
                textLayer.style.top = `${(pos.offsetTop + canvas.offsetTop)}px`;
                textLayer.style.height = canvas.offsetHeight + 'px';
                textLayer.style.width = canvas.offsetWidth + 'px';
                textLayer.style.position = 'absolute';
                //Add it to the web page
                pdfTextDiv.appendChild(textLayer);

                pdfStatus.innerHTML = `Loaded ${currPage} out of ${numPages} pages ...`;

                //Move to next page
                currPage++;
                if ( thePDF !== null && currPage <= numPages )
                {
                    thePDF.getPage(currPage).then(handlePages);
                }
                else
                {
                    pdfStatus.innerHTML = "";
                }  
            });    
    }
    
    //This is where you start
    pdfjsLib.getDocument(url).promise.then(function(pdf) 
    {
        //Set PDFJS global object (so we can easily access in our page functions
        thePDF = pdf;

        //How many pages it has
        numPages = pdf.numPages;

        //Start with first page
        pdf.getPage(currPage).then(handlePages);
    });    
}

// import { LaTeXJSComponent } from "https://cdn.jsdelivr.net/npm/latex.js/dist/latex.mjs"
// customElements.define("latex-js", LaTeXJSComponent);