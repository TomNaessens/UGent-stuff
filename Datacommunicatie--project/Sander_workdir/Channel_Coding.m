classdef Channel_Coding
    
    methods(Static=true)
        
        % Functies voor Hamming codering
        function bitenc = Ham_encode(bitstring)
            % Functie die een bitstring encodeerd met de (15,11) Hamming code.
            % input:
            % bitstring: vector van ongecodeerde bits met lengte 1xN
            
            n = 15; % Aantal codebits.
            k = 11; % Aantal informatiebits.
            
            bitstring = bitstring(:)';  % zorg ervoor dat de input een rijvector is
            N = length(bitstring);
            N_codewords = ceil(N/k);
            
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
                ];
            
            
            % [~,number_of_bits] = size(bitsrc); wordt blijkbaar al
            % gedaan hierboven.
            
            % Om onze informatiebits om te zetten naar codebits maken we gebruik van
            % een linaire transformatie (zoals beschreven op pagina 41).
            % Omdat we een (15,11) code hebben hebben we dus een veelvoud van 11 nodig
            % om een linaire transformatie te hebben.
            bitstring = [bitstring zeros(1, N_codewords*11-N)];
            
            
            
            % Het aanpassen van matrix (n,k) formaat
            bitstring = reshape(bitstring,k,[])';
            
            % Het encoderen van de informatiebits met een linaire
            % transforamtie.
            o = mod( bitstring * sys_generator,2);
            bitenc = o(:)';
            
            
            
            
            % door een geheel aantal codewoorden
            
            % wat dit doet.
            
            
            % output: de geencodeerde bits: lengte 15*N_codewords
            % bitenc = zeros(1, 15*N_codewords);
        end
        
        function bitdec = Ham_decode(bitenc)
            % Functie die een Hammingcode decodeerd (foutcorrectie)
            % input:
            % bitenc: vector met gecodeerde bits: lengte moet deelbaar zijn door 15
            
            bitenc = bitenc(:)';    % zorg ervoor dat de input een rijvector is
            N = length(bitenc);
            N_codewords = N/15;
            
            if(mod(N, 15) ~= 0)
                error('input is geen geheel aantal codewoorden.');
            end
            
            % Setup
                        
            % (15,11)
            k = 11;
            n = 15;
            
            
            informatiewoorden_dec = [0:2^k-1];
            informatiewoorden_bin = dec2bin(informatiewoorden_dec);
            
            
            
            
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
                1 1 1 0 1 0 1 1 0 0 1 0 0 0 1 ];
            
            all_codewoorden = mod(informatiewoorden_bin*sys_generator,2);
            
            % Het bepalen van de syndroomtabel e_{i}*H^{T} |coset leider
            coset_leider = zeros(1,n);
            coset_leider = vertcat(coset_leider,eye(n));
            
            syndroom_tabel = coset_leider*check_matrix';
            
            %output
            output =[];
            
            % Defineren van de syndroom lijst
            syndroom_lijst = [];
            
            % Dementies van bitstring
                                    
            codewoorden = reshape(bitenc, N_codewords,[]);
                        
            %%Opbouewn van de syndroom lijst (van onze codewoorden).
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
                    
                    % Het XOR (mod 2 optellen) van coset leider met
                    % ontvangen woord
                    codewoorden(syndroom_lijst_index,:) = ...
                        mod(codewoorden(syndroom_lijst_index,:) + coset_leider(syndroom_index,:),2);
                end
            end
            
            
            [a,b] = size(codewoorden);
            for i=1:a,
                informatie_index = find(ismember(all_codewoorden,codewoorden(i,1:end),'rows'),1);
                output = horzcat(output,informatiewoorden_bin(informatie_index,:));
            end
            
            
            
            bitdec = ~logical(output-'0');

            
            % output: de gedecodderde bits: lengte 11*N_codewords
            % bitdec = zeros(1, 11*N_codewords);
        end
        
        % Functies voor de productcode        
        
        function bitenc = Prod_encode(bitstring)
             % Functie die een bitstring encodeerd met de productcode.
            % input:
            % bitstring: vector van ongecodeerde bits met lengte 1xN
            
            bitstring = bitstring(:)';  % zorg ervoor dat de input een rijvector is
            N = length(bitstring);
            N_codewords = ceil(N/11/8);
            
            % voeg nullen aan de bitstring toe indien N niet deelbaar is
            % door een geheel aantal codewoorden
            bitstring = [bitstring zeros(1, N_codewords*11*8-N)];
            
            
            output = [];
            
            for i = 1 : N_codewords
			
				% Neem 8 informatiewoorden van 11 bits samen in een blok van 88 bits.
				% Daarop doen we hamming encoding, daardoor krijgen we 8 informatiewoorden van 15 bits.
			
				begin_index_row = ((i-1)*11*8)+1;	% Begin 
				end_index_row	=  i*11*8	;		% Eind
				r = Channel_Coding.Ham_encode(bitstring(1,begin_index_row : end_index_row));
                
                output = [output r];
                
				% Op dit blok voegen we dan pariteitsbits ( 15, 1 per kolom ) toe.
				
				for j = 1 : 15 % Som van de kolom berekenen
				
					parity = 0;
					
					start = (i-1)*15*9;	% Begin van de matrix
				
					for colindex = 1 : 8
						
						parity = mod(parity + output( start + ( (colindex-1)*15 ) + j),2);	% Be,gin van de matrix + juiste rij + verschuiving afhankelijk van welke kolom
					
					end					
					                    
					output = [output parity];
				
                end 
            end
            bitenc = output;
        end
        
        function bitdec = Prod_decode(bitenc)
            % Functie die een productcode decodeerd (foutcorrectie)
            % input:
            % bitenc: vector met gecodeerde bits: lengte moet deelbaar zijn door 15
            
            bitenc = bitenc(:)';    % zorg ervoor dat de input een rijvector is
            N = length(bitenc);
            N_codewords = N/15/(8+1);
            
            if(mod(N, 15*(8+1)) ~= 0)
                error('input is geen geheel aantal codewoorden.');
            end
            
            
            %% errorcorrectie hier
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
            
            syndroom_tabel = coset_leider*check_matrix';
           
            
            %verwerken van een codewoord. De opgave vertelt ons dat de input vector met
            %de codebits als componenten van de vorm is (l+1)*n -> (8+1) * 15
            
                                    
            % Defineer pariteit_bit_vector.
            pariteit_bit_vector = [];
            
            %%opdelen in rijen
            
            %bepaal de grote
            [a,b] = size(bitenc);
            
            % Eerste codewoord  slaan we al op.
            codewoorden = bitenc(1:15);
            t = 9;
            %verwerken van de codevector.
            for current_row=2:(b/n), 
                if current_row ~= t,
                sa = ((current_row)*n) - (n-1); %bepaal start index
                st = ((current_row)*n); %bepaal stop index
                codewoorden = vertcat(codewoorden,bitenc(sa:st)); %concat van codewoorden                                
                elseif current_row == t
                      t = t + 9;
                end
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
                    syndroom_lijst(i,:) = mod(syndroom_lijst(i,:),2);
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
                if sum(syndroom_lijst(syndroom_lijst_index,:)) > 0,
                    %index in de syndroom_tabel -> index in de coset leider tabel.
                    syndroom_index = find(ismember(syndroom_tabel,syndroom_lijst(syndroom_lijst_index:syndroom_lijst_index,1:end),'rows'),1);
                    
                    
                    % fout_bit_index
                    
                    % fprintf('fout in codewoord: %d met fout index: ',syndroom_lijst_index)
                    kolom_nr = find(coset_leider(syndroom_index:syndroom_index,1:end),1);
                    % fprintf('%d \n',kolom_nr)
                    
                    if codewoorden(syndroom_lijst_index:syndroom_lijst_index,kolom_nr:kolom_nr) == 1,
                        % fprintf('verbeteren van de fout\n')
                        
                        %verbeter de fout door XOR (optellen mod 2) van codewoord en
                        %coset leider
                        codewoorden(syndroom_lijst_index:syndroom_lijst_index,1:end) = ...
                            mod(codewoorden(syndroom_lijst_index:syndroom_lijst_index,1:end) + coset_leider(syndroom_index:syndroom_index,1,end),2);
                        
                        
                        %het syndroom in syndroom_lijst op null zetten (zoals staat
                        %beschreven in "Algoritme 1" pagina 4 van de opgave.
                        syndroom_vector = syndroom_lijst(syndroom_lijst_index,:);
                        syndroom_lijst(syndroom_lijst_index,:) = mod(syndroom_vector+syndroom_vector,2);
                    else
                        % fprintf('doen voorlopig niks...\n')
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
               % fprintf('geval 2\n');
                % We doen een XOR (optellen mod2) van het foute woord en de
                % pariteitbit vector, het corresenponderende foutieve pariteitbit zal
                % worden geflipt of worden aangezet.
                codewoorden(urow_index:urow_index,1:end) = mod(codewoorden(urow_index:urow_index,1:end) + pariteit_bit_vector,2);
                %verbeterende_codewoord = mod(codewoorden(urow_index:urow_index,1:end) + pariteit_bit_vector,2);
            else if aantal_niet_null == 2,
                    i1 = urow_index(1:1,1:1);
                    i2 = urow_index(2:2,1,1);
                    if syndroom_lijst(i1:i1,1:end) == syndroom_lijst(i2:i2,1:end),
                       % fprintf('geval 3\n');
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
            % Decoderen door ham_decode moet hier komen.
             bitdec = Channel_Coding.Ham_decode(codewoorden);                        
                    
        end
    end
end