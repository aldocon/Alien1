How this report is structured:

Folders:

content/ : This folder will contain all the chapters Lexer.tex Parser.tex ... and so on
images/  : This folder will contain all the pictures (If any is used) .jpg .png etc.
GroupProjectReport.tex : This uses \input{content/ChapterName.tex} to input the chapters into the main report
content/titlePage.tex  : This is the front page of the report (Very simple).

Files:

GroupProjectReport.tex.latexmain : File that specify the main file. Enable compilation of the whole document when editing a .tex file that is inputtet into the document. Like when editing content/Parser.tex and you just compile inside that document.
