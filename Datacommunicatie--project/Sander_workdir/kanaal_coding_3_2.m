%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%          VRAAG 3         %
%     Kanaalcodering       %
% Hamming code decoderen   %
% Sander Demeester         %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% Setup

% Input test vector, lengte 135 (een veelvoud van 15 (aantal codebits) om
% te testen.
input_vector = [0 1 1 0 0 1 0 0 1 1 1 1 0 0 1 1 0 0 1 0 1 0 1 1 1 1 1 1 1 1 0 1 1 0 0 0 0 1 1 1 1 1 1 1 1 1 1 0 0 0 1 0 1 1 0 1 1 1 0 1 1 1 1 1 1 0 0 0 0 0 0 1 0 0 1 0 0 1 1 1 0 1 1 1 1 0 1 1 0 0 1 0 1 0 0 1 1 1 0 1 0 0 1 1 1 1 0 1 1 0 1 1 0 1 1 0 1 1 0 0 1 1 0 1 0 1 1 0 0 0 0 1 1 0 0];


% (15,11)
k = 11;
n = 15;




% Systematische generator matrix van onze generator matrix.
sys_generator = [
    1 0 0 0 0 0 0 0 0 0 0 1 0 0 1 ;
    0 1 0 0 0 0 0 0 0 0 0 1 1 0 1 ;
    0 0 1 0 0 0 0 0 0 0 0 1 1 1 1 ;
    0 0 0 1 0 0 0 0 0 0 0 1 1 1 0 ;
    0 0 0 0 1 0 0 0 0 0 0 0 1 1 1 ;
    0 0 0 0 0 1 0 0 0 0 0 1 0 1 0 ;
    0 0 0 0 0 0 1 0 0 0 0 0 1 0 1 ;
    0 0 0 0 0 0 0 1 0 0 0 1 0 1 1 ;
    0 0 0 0 0 0 0 0 1 0 0 1 1 0 0 ;
    0 0 0 0 0 0 0 0 0 1 0 0 1 1 0 ;
    0 0 0 0 0 0 0 0 0 0 1 0 0 1 1 ;
    ];

% Check-matrix van onze generator veelterm
check_matrix = [
    1 1 1 1 0 1 0 1 1 0 0 1 0 0 0
    0 1 1 1 1 0 1 0 1 1 0 0 1 0 0
    0 0 1 1 1 1 0 1 0 1 1 0 0 1 0
    1 1 1 0 1 0 1 1 0 0 1 0 0 0 1 ];x

% Het bepalen van de syndroomtabel e_{i}*H^{T} |coset leider
coset_leider = zeros(1,n);
coset_leider = vertcat(coset_leider,eye(n));

syndroom_tabel = coset_leider*check_matrix';


% Defineren van de syndroom lijst
syndroom_lijst = [];

[i,j] = size(input_vector);

aantal_codewoorden = j/15;

codewoorden = reshape(input_vector, aantal_codewoorden,[]);

%%Opbouwen van de syndroom lijst (van onze codewoorden).
[a,b] = size(codewoorden);

% Zei iemand.. code hergebruiken?

%Bouw een lijst op met syndromen, we doen -1 omdat de laatste rij de
%pariteitbits zijn van de product code (dus geen codewoord)
for i=1:a,
    syndroom_lijst = vertcat(syndroom_lijst,(codewoorden(i:i,1:n)*check_matrix'));
    [~,b2] = size(syndroom_lijst);
    
    % Dit kan waarschijnlijk met een fancy matlab functie die ik nu niet
    % direct kan vinden.
    % We voeren een pseudo XOR operatie uit op onze elementen.
    for ii=1:b2,
        syndroom_lijst(i:i,ii:ii) = mod(syndroom_lijst(i:i,ii:ii),2);
    end
end


% Nu we alle syndromen hebben gaan we zoeken naar niet null vectoren en
% deze verbeteren, zeer analoog met kanaal_coding_5.mr syndroom_lijst_index=1:a,

[a,b] = size(syndroom_lijst);
for syndroom_lijst_index=1:a
    
    % als de som van alle componenten in de syndroom groter is dan 0 dan
    % hbben we een fout.
    if sum(syndroom_lijst(syndroom_lijst_index:syndroom_lijst_index,1:end)) > 0,
        %index in de syndroom_tabel -> index in de coset leider tabel.
        syndroom_index = find(ismember(syndroom_tabel,syndroom_lijst(syndroom_lijst_index:syndroom_lijst_index,1:end),'rows'),1);
        
        codewoorden(syndroom_lijst_index:syndroom_lijst_index,1:end) = ...
            mod(codewoorden(syndroom_lijst_index:syndroom_lijst_index,1:end) + coset_leider(syndroom_index:syndroom_index,1,end),2);
    end
end



