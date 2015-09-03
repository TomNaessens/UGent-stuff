
all: build/stemmer/Stemmer.class

run: build/stemmer/Stemmer.class
	echo sudo pcscd -f
	java -ea -cp build/:lib/* stemmer.Stemmer $(pin)

jar: all dist/prototype.jar

runjar: jar
	java -cp dist/prototype.jar:lib/jackson-core-2.2.3.jar:lib/jackson-databind-2.2.3.jar:lib/jackson-annotations-2.2.3.jar:lib/jEidlib.jar stemmer.Stemmer

clean:
	rm -rf dist/ build/
	mkdir dist/
	mkdir build/

build/stemmer/Stemmer.class: src/stemmer/Stemmer.java build/stemmer/gui/Venster.class build/stemmer/Bijzitter.class build/stemmer/Stembus.class
#build/stemmer/Stemmer.class: src/stemmer/Stemmer.java build/stemmer/gui/Venster.class build/stemmer/Bijzitter.class
	javac -Xlint -cp build/ -d build/ $<

build/stemmer/gui/Venster.class: src/stemmer/gui/Venster.java build/stemmer/VotingForm.class build/stemmer/Bijzitter.class build/stemmer/Vote.class  build/stemmer/Exceptions.class build/stemmer/Stembus.class
	javac -Xlint -cp build/:lib/swing-layout-1.0.4.jar -d build/ $<

build/stemmer/VotingForm.class: src/stemmer/VotingForm.java
	javac -Xlint -d build/ $<

build/stemmer/Bijzitter.class: src/stemmer/Bijzitter.java build/stemmer/VotingForm.class build/ssl/VotingSSLFactory.class build/stemmer/VotingProof.class build/stemmer/Exceptions.class
	javac -Xlint -cp build/:lib/jackson-core-2.2.3.jar:lib/jackson-databind-2.2.3.jar/:lib/jEidlib.jar -d build/ $<

build/ssl/VotingSSLFactory.class: src/ssl/VotingSSLFactory.java
	javac -Xlint -d build/ $<

build/stemmer/Stembus.class: src/stemmer/Stembus.java build/stemmer/Vote.class
	javac -Xlint -cp build/:lib/jackson-core-2.2.3.jar:lib/jackson-databind-2.2.3.jar -d build/ $<

build/stemmer/Vote.class: src/stemmer/Vote.java
	javac -Xlint -cp lib/jackson-core-2.2.3.jar:lib/jackson-databind-2.2.3.jar:lib/jEidlib.jar:lib/gnu-crypto.jar -d build/ $<

dist/prototype.jar: META-INF/MANIFEST.MF lib/jackson-core-2.2.3.jar lib/jackson-databind-2.2.3.jar lib/jackson-annotations-2.2.3.jar lib/jEidlib.jar lib/gnu-crypto.jar certs/bijzitter.jks certs/stembus.jks
	find build/ -name '*.class' | sed 's_^build/_-C build/ _' | xargs jar cvfm dist/prototype.jar $^

build/stemmer/VotingProof.class: src/stemmer/VotingProof.java
	javac -Xlint -d build/ $<

build/stemmer/Exceptions.class: src/stemmer/Exceptions.java
	javac -Xlint -d build/ $<
