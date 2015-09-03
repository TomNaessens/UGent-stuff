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
            
            % Good programming practice: stel dat een gebruiker in plaats
            % van de rel_freq, de abs_freq mee geeft zal deze functie niet
            % falen.
            rel_freq = rel_freq/sum(rel_freq);
            
            % OO in Matlab, yuy!
            % We stellen eerst een array van nodes op en sorteren deze
            % volgens frequentie.
            node_array(N) = node;
            for i = 1:N
                node_array(i).value = alphabet(i);
                node_array(i).freq = rel_freq(i);
                node_array(i).is_leaf = 1;
            end
            
            
            % We sorteren nu N-1 keer de array, en hangen de laatste twee
            % Nodes samen aan een nieuwe node die we op plaats N-1 plaatsen
            % enzovoort, enzoverder.
            % Uiteindelijk blijft er nog 1 node over: de rootnode met als
            % frequentie 1. De rest van de nodes zitten in de boom.
            aantal_nodes = N;
            
            for i=aantal_nodes:-1:2
                node_array=sort(node_array); 
            
                rechts = node_array(i);
                links = node_array(i-1);
                
                parent = node;
                parent.value = 0; % Heeft geen value nodig.
                parent.freq = links.freq + rechts.freq;
                parent.is_leaf = 0; % Inner nodes ftw.
            
            
                parent.left = links;
                parent.right = rechts;
                
                node_array(i-1) = parent;
            end
            
            % We stellen de boom op aan de hand van de functie
            % generate_codes
            root = node_array(1);
            code_array = cell(16,1);         
            % Met een transpose zodat de output in hetzelfde formaat als de
            % voorbeeldoutput staat
            codewords = Source_Coding.generate_codes(root, [], code_array).';
        end

        % Recursieve hulpfunctie om de codes op te stellen
        function code_array = generate_codes(node, code, code_array)
            if node.is_leaf == 1
                % Een leaf: voeg toe aan de code_array
                letter = node.value;
                code_array{letter} = code;
            else
                % Geen leaf: opsplitsen in links en rechts: we voegen links
                % een 0 toe en rechts een 1 aan de code.
                code_array = Source_Coding.generate_codes(node.left, [code 0], code_array);
                code_array = Source_Coding.generate_codes(node.right, [code 1], code_array);
            end
        end
        
        % Op te roepen met:
        % Source_Coding.create_canonical_codebook(alphabet,
        % cellfun('length',codewords))
        function codewords = create_canonical_codebook(alphabet, lengths)
            % Functie die de Cononical Huffmancode opstelt voor gegeven alfabet en
            % codelengtes
            % input:
            % alphabet: 1xN cell array vb alphabet = {'A', 'B', 'C', 'D'}
            % lengths: lengtes van elk codewoord: [1 3 2 3];
            
            N = numel(alphabet);
            
            % We stellen eerst een matrix op met 2 kolommen: de eerste
            % bevat de codewoorden, de tweede de lengte van de codewoorden.
            % Deze sorteren we eerst volgens de lengtes en
            % daarna volgens de codewoorden, zoals opgegeven in de opgave.
            sorted_matrix = sortrows([transpose(alphabet) transpose(lengths)],[2 1]);
           
            % Startcode:
            counter = 0;
            codewords = cell(16,1);
            code = de2bi(counter);
            
            for i = 1:N
                % Voor elke code berekenen we binare weergave in arrayvorm met
                % de meest significante bit links.
                code = de2bi(counter, 'left-msb');
                % We padden deze code tot aan de lengte
                code = [code (zeros(1, sorted_matrix(i, 2) - length(code)))];
                % En we voegen deze op zijn bijhorende plaats toe aan de
                % codewords array
                codewords{sorted_matrix(i, 1)} = code;
                % We berekenen de teller opnieuw aangezien deze kan
                % veranderd zijn door de padding zeros en verhogen deze
                % uiteindelijk met 1.
                counter = bi2de(code, 'left-msb') + 1;
            end
            
            % output the codewords
            % example: codewords = {[0], [1 1 0], [1 0], [1 1 1]};
            % Ook hier nog een transpose om overeen te komen met de
            % voorbeeldoutput
            codewords = codewords.'
        end
      
        
        % Functies voor het encoderen/decoderen
        function compressed = Huffman_encode(data, alphabet, codewords)
            % Functie die een bitstring comprimeert met een Huffmancode
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