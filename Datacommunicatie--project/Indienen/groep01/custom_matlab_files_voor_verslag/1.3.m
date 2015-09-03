%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%          VRAAG 3         %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
load('Xfile4.mat')      % laad bestand in (rij van bits)
format long             % zet het formaat op long

H = zeros(10,1);        % maak lege rij voor de entropie voor alle k
ref_entr = zeros(10,1); % maak lege rij voor de entropie voor alle k van de referentie

kk = zeros(10,1);

input_size = numel(bitsrc); % aantal bronsymbolen

for k=1:10,             % k is het aantal bits dat we samennemen in 1 macrosymbool
    freq_tabel = zeros(1,2^k);  % maak abs frequentietabel aan (1 kolom 2^k rijen)
    ref_freq = ones(1,2^k)/2^k; % maak referentie rel freqtabel aan (alles even waarsch)
    
    % bepaal absolute frequentie
    for i=1:input_size/k,       % i = 1..aantal macroblokken
        index = (bi2de(bitsrc(((i-1)*k)+1:k*i)))+1; % lees macroblok naar waarde
        freq_tabel(index) = freq_tabel(index) + 1;  % verhoog de freq van macroblok index
    end

    freq_tabel = freq_tabel/(input_size/k); % zet abs freq om naar rel freq 

    % pas formule entropie toe
    H(k) = -sum(freq_tabel(freq_tabel~=0).*log2(freq_tabel(freq_tabel~=0)));
    ref_entr(k) = -sum(ref_freq.*log2(ref_freq));
end

% Toon een plot
waarden_x_as=1:1:10;

plot(waarden_x_as, ref_entr, '-go', waarden_x_as, H, '-bo');
title('Opgave 3: Entropie ten opzichte van aantal samengenomen bits');
xlabel('Aantal bits per macrosymbool');
ylabel('Entropie');
leg1 = legend('Referentie', 'Geobserveerde');
set(leg1,'Location','NorthWest')