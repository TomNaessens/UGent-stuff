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
            
            % Om onze informatiebits om te zetten naar codebits maken we gebruik van
            % een linaire transformatie (zoals beschreven op pagina 41).
            % Omdat we een (15,11) code hebben hebben we dus een veelvoud van 11 nodig
            % om een lineaire transformatie te hebben.
            bitstring = [bitstring zeros(1, N_codewords*11-N)];
            
            
            
            % Het aanpassen van matrix (n,k) formaat
            bitstring = reshape(bitstring,k,[])';
            
            % Het encoderen van de informatiebits met een lineaire
            % transformatie.
            o = mod( bitstring * sys_generator,2);
            bitenc = o(:)';
            
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
            
            % Definieren van de syndroom lijst
            syndroom_lijst = [];
            
            % Dimensie van bitstring
            
            codewoorden = reshape(bitenc, N_codewords,[]);
            
            % Opbouwen van de syndroom lijst van onze codewoorden.
            [a,b] = size(codewoorden);
            
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
            
        end
        
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
                        
                        parity = mod(parity + output( start + ( (colindex-1)*15 ) + j),2);	% Begin van de matrix + juiste rij + verschuiving afhankelijk van welke kolom
                        
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
            
            % errorcorrectie hier
            
            transposed_check_matrix = ...
                transpose([
                1 1 1 1 0 1 0 1 1 0 0 1 0 0 0;
                0 1 1 1 1 0 1 0 1 1 0 0 1 0 0;
                0 0 1 1 1 1 0 1 0 1 1 0 0 1 0;
                1 1 1 0 1 0 1 1 0 0 1 0 0 0 1;
                ]);
            
            syndrome_table = ...
                [
                0 0 0 0;
                1 0 0 1;
                1 1 0 1;
                1 1 1 1;
                1 1 1 0;
                0 1 1 1;
                1 0 1 0;
                0 1 0 1;
                1 0 1 1;
                1 1 0 0;
                0 1 1 0;
                0 0 1 1;
                1 0 0 0;
                0 1 0 0;
                0 0 1 0;
                0 0 0 1;
                ];
            
            aantal_informatie_bits = 4;
            
            current_line = [];
            
            for i = 1:N_codewords
                
                begin_index = ((i-1)*135)+1;	% Alle vorige matrixes bij incrementen
                end_index = begin_index + 134;
                
                currentMatrix = vec2mat(bitenc(begin_index:end_index),15);	% Maak er een matrix van
            
				parities		=	currentMatrix(1:end-1,:);					     			% De pariteiten die in we in de matrix vinden				
				calculated_parities = mod((currentMatrix' * ones(size(currentMatrix,1),1)), 2)';	% Bereken voor elke kolom de pariteiten
                
                syndromes 		= 	bi2de(mod(parities*transposed_check_matrix,2),'left-msb');	% Bereken syndromen, maak decimaal van om 0 te checken met find
                
                indexes_of_errors = find(syndromes);	% Find geeft terug waar het niet nul is
                
                for j = 1:size(indexes_of_errors)		% Voor elke fout
                    
                    coset_leider = syndrome_table(syndromes(indexes_of_errors(j))+1,:);
                    
                    % Als uitgerekende pariteit 1 is -> corrigeer
                    
                    col_error_index = find(coset_leider,1);
                    
                    if(calculated_parities(1,col_error_index))
                        parities(indexes_of_errors(j),col_error_index)	=	mod(parities(indexes_of_errors(j),col_error_index) + 1,2);	% Flip het bitje
                        
                        calculated_parities(1,col_error_index) = 0;
                        syndromes(indexes_of_errors(j)) = 0;
                    end
                    
                end
                
                indexes_of_errors = find(syndromes);	% Dit doen we weer eens
                
                % Indien er slechts 1 syndroom verschillend is van nul, dan komen er twee fouten voor in die bepaalde rij.
                if(size(indexes_of_errors,1) == 1)
                    
					parities(indexes_of_errors(1,1),:) = mod(parities(indexes_of_errors(1,1),:) + calculated_parities, 2); % De XOR nemen
                    
                    % Indien er 2 syndromen zijn die verschillen van nul en bovendien gelijk zijn aan elkaar, betekent dit dat er 2 fouten optreden in 1 kolom.
                elseif((size(indexes_of_errors,1) == 2) & syndromes(indexes_of_errors(1,1)) == syndromes(indexes_of_errors(2,1)))
                    
					column_index = find(syndrome_table(syndromes(indexes_of_errors(1,1)) + 1, :));
                    parities(indexes_of_errors(1,1),column_index)	=	mod(parities(indexes_of_errors(1,1), column_index) + 1, 2);
                    parities(indexes_of_errors(2,1),column_index)	=	mod(parities(indexes_of_errors(2,1), column_index) + 1, 2);
                    
                end
                
                outputparities = parities(:,1:15);
                current_line = [current_line reshape(outputparities', 1, [])];
            end
            bitdec = Channel_Coding.Ham_decode(current_line);
        end
    end
end