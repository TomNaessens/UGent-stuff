rm *.java *.class
antlr4 Pract3.g4
javac -cp /Library/Caches/Homebrew/antlr-4.5.jar Pract3*.java
cat bibtex_correct.bib | grun Pract3 bibtex #-gui
