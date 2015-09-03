%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%          VRAAG 5         %
%     Kanaalcodering       %
%     Sander Demeester     %
% Decoderen product code   %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clear;

%Setup
l = 8; %De product code gaat l x k informatie bits omzetten naar (l+1)*n, we kiezen l gelijk aan 8.
n = 15; %van 15,11 code



% Systematische generator matrix
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
]; %rechtstreeks van dropbox

% Check-matrix
check_matrix = [
1 1 1 1 0 1 0 1 1 0 0 1 0 0 0
0 1 1 1 1 0 1 0 1 1 0 0 1 0 0
0 0 1 1 1 1 0 1 0 1 1 0 0 1 0
1 1 1 0 1 0 1 1 0 0 1 0 0 0 1 ]; %dropbox

% Het bepalen van de syndroomtabel e_{i}*H^{T} |coset leider

coset_leider = zeros(1,n);
coset_leider = vertcat(coset_leider,eye(n));

syndroom_tabel = coset_leider*check_matrix'


%verwerken van een codewoord. De opgave vertelt ons dat de input vector met
%de codebits als componenten van de vorm is (l+1)*n -> (8+1) * 15

%als voorbeeld om mee te werken construeren we een vector die voldoet aan
%deze dementies. 

%codewoord vector met 135bits als componenten

input_vector = [0 1 1 0 0 1 0 0 1 1 1 1 0 0 1 1 0 0 1 0 1 0 1 1 1 1 1 1 1 1 0 1 1 0 0 0 0 1 1 1 1 1 1 1 1 1 1 0 0 0 1 0 1 1 0 1 1 1 0 1 1 1 1 1 1 0 0 0 0 0 0 1 0 0 1 0 0 1 1 1 0 1 1 1 1 0 1 1 0 0 1 0 1 0 0 1 1 1 0 1 0 0 1 1 1 1 0 1 1 0 1 1 0 1 1 0 1 1 0 0 1 1 0 1 0 1 1 0 0 0 0 1 1 0 0];

% Defineer pariteit_bit_vector.
pariteit_bit_vector = [];

% opdelen in rijen

%bepaal de grote
[a,b] = size(input_vector);

% Eerste codewoord  slaan we al op.
codewoorden = input_vector(1:15); 

%verwerken van de codevector.
for current_row=2:(b/n)
    sa = ((current_row)*n) - (n-1); %bepaal start index
    st = (current_row)*n; %bepaal stop index
    
    codewoorden = vertcat(codewoorden,input_vector(sa:st)); %concat van codewoorden
end

%de laatste rij is de rij met partiteitbits van de product code (zie vorige
%opgave).


%%Opbouewn van de syndroom lijst (van onze codewoorden).
syndroom_lijst = codewoorden(1:1,1:n)*check_matrix';


%Bouw een lijst op met syndromen, we doen -1 omdat de laatste rij de
%pariteitbits zijn van de product code (dus geen codewoord)
for i=2:(b/n)-1,
    syndroom_lijst = vertcat(syndroom_lijst,(codewoorden(i:i,1:n)*check_matrix'));
    [a,b] = size(syndroom_lijst);
    
    % Dit kan waarschijnlijk met een fancy matlab functie die ik nu niet
    % direct kan vinden.
    % We voeren een pseudo XOR operatie uit op onze elementen.
    for ii=1:b, 
        syndroom_lijst(i:i,ii:ii) = mod(syndroom_lijst(i:i,ii:ii),2);
    end
end

% pseudo xor operatie onze componenten in onze lijst van syndromen voor
% onze eerste tabel
  for ii=1:b, 
        syndroom_lijst(1:1,ii:ii) = mod(syndroom_lijst(1:1,ii:ii),2);
  end
  
  % We bepalen de pariteitbits van onze vectoren in onze codewoorden matrix
  % (deze zijn toegevoegd door de product code)
  % De code hieronder is zeer sterk gebaseerd of de code die sander (ik)
  % gebruikt heb om de code op te stellen. We weten dat de laatste rij de
  % rij is met pariteitbits.
  
  [a,b] = size(codewoorden); % Bepalen van de dementies
  
  
  for i=1:b
      % Bepaal pariteitbit van alle kolom vectoren in onze codewoorden      
      pariteit_bit_vector = horzcat(pariteit_bit_vector,mod(sum(codewoorden(i:a,b:b)),2)); 
  end
         
  %Voor onze test vector is dit helaas allemaal fout :( slecht kanaal!
  
  % Hier zal het algoritme moeten beginnen een keuze maken, welke woorden

  %we overlopen alle syndroomen in onze syndroom lijst, van
  %1,...,|syndroom_lijst| met index i, als syndroom_lijst[i] != {0,...,0}^t
  %dan is het ontvangen woord codewoorden[i] fout.
  
  [a,b] = size(syndroom_lijst);
  for syndroom_lijst_index=1:a,
      
      % als de som van alle componenten in de syndroom groter is dan 0 dan
      % hbben we een fout.
      if sum(syndroom_lijst(syndroom_lijst_index:syndroom_lijst_index,1:end)) > 0,
          %index in de syndroom_tabel -> index in de coset leider tabel.
          syndroom_index = find(ismember(syndroom_tabel,syndroom_lijst(syndroom_lijst_index:syndroom_lijst_index,1:end),'rows'),1);
          
          
          % fout_bit_index
          
          fprintf('fout in codewoord: %d met fout index: ',syndroom_lijst_index)
          kolom_nr = find(coset_leider(syndroom_index:syndroom_index,1:end),1);
          fprintf('%d \n',kolom_nr)
          
          if codewoorden(syndroom_lijst_index:syndroom_lijst_index,kolom_nr:kolom_nr) == 1,
                fprintf('verbeteren van de fout\n')
              
                %verbeter de fout door XOR (optellen mod 2) van codewoord en
                %coset leider
                codewoorden(syndroom_lijst_index:syndroom_lijst_index,1:end) = ...
                    mod(codewoorden(syndroom_lijst_index:syndroom_lijst_index,1:end) + coset_leider(syndroom_index:syndroom_index,1,end),2);
                
                
                %het syndroom in syndroom_lijst op null zetten (zoals staat
                %beschreven in "Algoritme 1" pagina 4 van de opgave.
                syndroom_vector = syndroom_lijst(syndroom_lijst_index:syndroom_lijst_index,1:end);
                syndroom_lijst(syndroom_lijst_index:syndroom_lijst_index,1:end) = mod(syndroom_vector+syndroom_vector,2);
          else
                fprintf('doen voorlopig niks...\n')
          end
      end
  end
  
  
  % Volgens het algoritme moeten we 3 gevallen onderscheiden.
  % 1. Meer dan 2 syndromen verschillen van 0 -> doe niks
  % 2. 1 syndroom verschillende van 0, verbeter.
  % 3. 2 syndromen zijn verschillend van 0 EN zijn aan elkaar GELIJK
  
  [row_index,~,~] = find(syndroom_lijst);
  [aantal_niet_null,~] = size(unique(row_index));
  urow_index = unique(row_index);
  
  
  % Ik moet deze verschillende gevallen nog implemeteren, ik ga dit
  % zaterdag (morgen) doen, nog wat leeswerk dat ik zeker niks fout doe.
  if aantal_niet_null == 1,
      fprintf('geval 2\n');
      % We doen een XOR (optellen mod2) van het foute woord en de
      % pariteitbit vector, het corresenponderende foutieve pariteitbit zal
      % worden geflipt of worden aangezet.
      codewoorden(urow_index:urow_index,1:end) = mod(codewoorden(urow_index:urow_index,1:end) + pariteit_bit_vector,2);
      %verbeterende_codewoord = mod(codewoorden(urow_index:urow_index,1:end) + pariteit_bit_vector,2);
  else if aantal_niet_null == 2,
          i1 = urow_index(1:1,1:1);
          i2 = urow_index(2:2,1,1);
          if syndroom_lijst(i1:i1,1:end) == syndroom_lijst(i2:i2,1:end),           
              fprintf('geval 3\n');
              % De elementen van urow_index vector vertellen ons wat de
              % indexen zijn van de foutieve rij vectoren.
              % Bepaal de kolom indexen van de fouten
              kolom = find(syndroom_lijst(urow_index(1)));
              % We gebruiken +1 omdat we een bit willen flippen met een XOR
              % (optelling mod2)
              codewoorden(i1,kolom) = mod(codewoorden(i1,kolom)+1,2); % Verbeteren van het eerste foutief codewoord
              codewoorden(i2,kolom) = mod(codewoorden(i2,kolom)+1,2); % Verbeteren van het tweede foutief codewoord
          end
      end
  end
          % Decoderen door ham_decode
  
  
  

