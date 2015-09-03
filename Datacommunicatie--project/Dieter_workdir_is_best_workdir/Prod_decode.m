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
            
			transposed_check_matrix = 
			transpose([
				1 1 1 1 0 1 0 1 1 0 0 1 0 0 0;
                0 1 1 1 1 0 1 0 1 1 0 0 1 0 0;
                0 0 1 1 1 1 0 1 0 1 1 0 0 1 0;
                1 1 1 0 1 0 1 1 0 0 1 0 0 0 1;

			]);			
		
            syndrome_table = 
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
			
			bitdec = [];
			
            for i = 1:N_codewords
			
                begin_index = ((i-1)*135)+1;	% Alle vorige matrixes bij incrementen
                end_index = begin_index + 134;
				
                currentMatrix = vec2mat(bitenc(begin_index:end_index),15);	% Maak er een matrix van
                
                calculated_parities = mod((currentMatrix' * ones(size(currentMatrix,1),1)), 2)';	% Bereken voor elke kolom de pariteiten
                parities		=	currentMatrix(1:end-1,:);					     			% De pariteiten die in we in de matrix vinden
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
				
                outputparities = parities(:,1:aantal_informatie_bits);	
                bitdec = [bitdec reshape(outputparities', 1, [])];
            end
    end