classdef Source_Coding
          
    methods(Static=true)
        
        % Functies voor de Huffmancode op te stellen
        function codewords = create_codebook(alphabet, rel_freq)
            % Functie die de Huffmancode opstelt voor gegeven alfabet en
            % relative frequenties
            % input:
            % alphabet: 1xN cell array vb alphabet = {'A', 'B', 'C', 'D'}
            % rel_freq: relative frequenties voor elke letter in het
            % alfabet: 1xN vector vb: rel_freq = [0.5 0.1 0.3 0.1];
            
            N = numel(alphabet);
            rel_freq = rel_freq/sum(rel_freq);
            
            
            %output the codewords
            % example: codewords = {[0], [1 1 0], [1 0], [1 1 1]};
            new_symbols = cell(1, N);
            
        end

        function codewords = create_canonical_codebook(alphabet, lengths)
            % Functie die de Cononical Huffmancode opstelt voor gegeven alfabet en
            % codelengtes
            % input:
            % alphabet: 1xN cell array vb alphabet = {'A', 'B', 'C', 'D'}
            % lengths: lengtes van elk codewoord: [1 3 2 3];
            
            N = numel(alphabet);
            
            
            % output the codewords
            % example: codewords = {[0], [1 1 0], [1 0], [1 1 1]};
            codewords = cell(1, N);
        end
      
        
        % Functies voor het encoderen/decoderen
        function compressed = Huffman_encode(data, alphabet, codewords)
            % Functie die een bitstring comprimeerd met een Huffmancode
            % input:
            % data: de data die gecomprimeerd moet worden
            % alphabet: cell array of rijvector met alle mogelijke symbolen 
            % codewords: cell array met de codewoorden voor elke letter in
            % het alfabet.
            
            N = length(data);
            N_symbols = length(alphabet);            
            
            if iscell(alphabet) && max(cellfun(@length, alphabet))>1
                error('ERROR: een symbool uit het alfabet mag maar 1 cijfer of alfanumerieke waarde bevatten');
            end
            
            if ischar(data)                
                % converteer de alfanumerieke waardes naar numeriek waardes
                numeric_data = double(data);
                numeric_symbols =  cellfun(@double, alphabet);                             
            elseif isrow(data)
                numeric_data = data;
                if iscell(alphabet),    numeric_symbols = cell2mat(alphabet);     
                else numeric_symbols = alphabet;     
                end
            else
                error('ERROR: input moet ofwel een rijvector of een karakater-string zijn');
            end    
             
            % De kern van deze functie: vervang elke letter uit het alfabet 
            % met het corresponderend codewoord            
            compressed = cell(1,N);
            for n=1:N_symbols
                idx = numeric_data==numeric_symbols(n);
                compressed(idx) = {codewords{n}};
            end
            
            % Als er nog lege cellen overblijven wil dit zeggen dat het
            % woordenboek niet alle mogelijke symbolen uit de data heeft.
            if nnz(cellfun(@isempty,compressed))
                error('ERROR: woordenboek incompleet');
            end
                   
            % zet om naar een rijvector
            compressed = cell2mat(compressed);            
            
        end
        
        function decompressed = Huffman_decode(data_compressed, alphabet, codebook)
            % Functie die een gecomprimeerde bitsequentie decomprimeerd
            % Optimaal werkt deze functie met een boom maar hier
            % decomprimeren we simpelweg door te itereren.
            % input
            % data_compressed
            % alphabet: cell array of rijvector met alle mogelijke symbolen 
            % codewords: cell array met de codewoorden voor elke letter in
            % het alfabet.
            
            N = length(data_compressed);
            
            % voorbereiding: splits de codewoorden op per lengte
            lengths = cellfun(@length, codebook);
            max_len = max(lengths);
                
            cl = cell(1,max_len);
            idxl = cell(1,max_len);
            for l=1:max_len
                idx_l = find(lengths==l);
                % zet de codewoorden van lengte l om naar hun decimale vorm                
                cl{l} = cellfun(@bi2de, codebook(idx_l));
                idxl{l} = idx_l;
            end                      
            
            % decompressie: doorloop de data en zoek naar codewoorden
            output = [];    % bevat de indices van de letters die herkend zijn.
            idx = 1;        % index in de data
            window = 1;     % bereik waarover we zoeken: we beginnen met zoeken naar codewoorden van lengte 1
            while idx+window <= N+1
                idx_code = find(cl{window} == bi2de(data_compressed(idx:idx+window-1)));
                if ~isempty(idx_code)    
                    %codewoord gevonden, voeg dit toe aan de output en ga verder
                    output = [output idxl{window}(idx_code)];                     
                    idx = idx + window;
                    window = 1;
                else
                    % nog geen codewoord gevonden; vergroot het bereik
                    window = window+1;
                end
            end
                      
            % zet de output om naar letters uit het alfabet
            decompressed = alphabet(output);
            
        end
        
        
    end
    
end