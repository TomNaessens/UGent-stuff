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
            
            bitenc = [];
            for i = 1 : N_codewords
			
				% Neem 8 informatiewoorden van 11 bits samen in een blok van 88 bits.
				% Daarop doen we hamming encoding, daardoor krijgen we 8 informatiewoorden van 15 bits.
			
				begin_index_row = ((i-1)*11*8)+1;	% Begin 
				end_index_row	=  i*11*8;			% Eind
				
                bitenc = [bitenc Channel_Coding.Ham_encode(bitstring(1,begin_index_row : end_index_row))];
                
				% Op dit blok voegen we dan pariteitsbits ( 15, 1 per kolom ) toe.
				
				for j = 1 : 15 % Som van de kolom berekenen
				
					parity = 0;
					
					start = (i-1)*15*9;	% Begin van de matrix
				
					for colindex = 1 : 8
						
						parity = parity + bitenc( start + ( (colindex-1)*15 ) + j);	% Begin van de matrix + juiste rij + verschuiving afhankelijk van welke kolom
					
					end
						
					parity = mod(parity,2);	
					bitenc = [bitenc parity];
				
				end
			end
 end