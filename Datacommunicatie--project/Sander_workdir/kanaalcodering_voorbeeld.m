%Kanaal coding uitgewerkt voorbeeld voor een (6,3) code%

%Encodeer tabel
% a = (a1,a2,a3,a1+a2+a3,a1+a2,a1)
encodeertabel = [0 0 0 0 0 0 0 0 0 ; 0 0 1 0 0 1 1 0 0 ; 0 1 0 0 1 0 1 1 0 ; 0 1 1 0 1 1 0 1 0 ; 1 0 0 1 0 0 1 1 1 ; 1 0 1 1 0 1 0 1 1 ; 1 1 0 1 1 0 0 0 1 ; 1 1 1 1 1 1 1 0 1 ]

%informatiewoorden 
informatiewoorden = encodeertabel(1:end,1:3)

%De hamming afstand is d_h (a,b) is het aantal pos waarin beide codewoorden
%van elkaar verschillen.

%Uit 2^n mogelijk codes selecteren we er 2^k
%In ons geval n=6 en k=3->8 dus.
codewoorden = encodeertabel(1:end,4:end)

%De som mod 2 van 2 codewoorden is terug een codeword
% Vb: 
codewoorden(1:end,1) + codewoorden(1:end,2)
%Is gelijk aan 
codewoorden(1:end,5) % mod2

%de mod 2 som van twee codewoorden is terug een codewoord, hieruit volgt
%dat elke mogelijke linaire combinatie (mod 2) van een code woord terug  een codewoord vormt. 
%Dit betekent, omdat de informatiebits onafhankelijk zijn we k (3)
%codewoorden kunnen vinden die corresponderen met een informatiecodewoord waar
%de pariteit 1 van is. Met deze k codewoorden kunnen we dan alle 2^k andere
%codewoorden vormen door 2^k linaire combinaties te namen van deze k
%basiscodewooren. (linaire vectorruimte).
%Dit is onze generator matrix
G = encodeertabel(5,4:end);
G = vertcat(G,encodeertabel(3,4:end));
G = vertcat(G,encodeertabel(2,4:end));

% G spant onze vector ruimte (codewoorden) op.

eq(informatiewoorden(2,1:end)*G,codewoorden(2,1:end))

%Fout correctie en fout detectie.
%Omdat een decodeertabel veel te groot is zullen we gebruik maken van een
%check matrix.
%G zijn de basisvectoren voor onze k-dimensionale vector ruimte. Dit is een
%subvector ruimte van de n-demensionale vectorruimte.
%We kunnen voor elke subruimte een nulruimte defineren die, zodat elke
%vector in de nulruimte orthogonaal is met elke vector in de
%oorspronkelijke ruimte. De nullruimte heeft een dem van n-k

%We noemen de nulruimte voor onze code de duale code
%De generator matrix voor deze duale code noemen we checkmatrix. H
%Aangezien elk codewoord in de oorspronkelijke code orthonaal is met elk
%codewoord uit de nulruimte zal een linaire combinatie nul zijn.

 H = [ 1 1 1 1 0 0 ; 1 1 0 0 1 0 ; 1 0 0 0 0 1 ]
% De checkmatrix bevat de zelfde informatie over het codewoord.
% Er geldt dus G*H^t = 0 (mod 2)
G*H'
%Een codewoord is dus een vector in de linaire vector ruimte opgespannen
%door G
codewoorden * H'

%vb uit curcus:
H(1:3,4) + H(1:3,4)

%een fout vector: e
%ontvangen woord: r
e = [0 0 0 0 1 1 ]
r =  (codewoorden(3,1:end) + e)

%Omdat het product van rH^T enkel info bevat over de foutvector en niet
%over het codewoord (het product daarvan is nl 0).
%We definerne het syndroom van r als: 
s = r*H'



