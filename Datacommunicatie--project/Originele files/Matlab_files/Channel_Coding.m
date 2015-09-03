
classdef Channel_Coding
          
   methods(Static=true)
        
        % Functies voor Hamming codering
        function bitenc = Ham_encode(bitstring)
            % Functie die een bitstring encodeerd met de (11,15) Hamming code.
            % input:
            % bitstring: vector van ongecodeerde bits met lengte 1xN
            
            bitstring = bitstring(:)';  % zorg ervoor dat de input een rijvector is
            N = length(bitstring);
            N_codewords = ceil(N/11);            
            
            % voeg nullen aan de bitstring toe indien N niet deelbaar is
            % door een geheel aantal codewoorden
            bitstring = [bitstring zeros(1, N_codewords*11-N)];

                       
            
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

            % Product code hier
            
            % output:
            % bitenc = zeros(1, (8+1)*15*N_codewords);
            
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
            
            
            % output: de gedecodderde bits: lengte 11*8*N_codewords
            % bitdec = zeros(1, 11*8*N_codewords);
        end
        
        
    end
    
end