function huffman_dict = freq(source,aantal_bron_symbolen)
    freq_tabel = zeros(1,2^aantal_bron_symbolen);
    input_size = numel(source);
    
    alphabet = [1:2^aantal_bron_symbolen];
    
    for i=1:input_size/aantal_bron_symbolen, %Loop over de input per aantal bronsymbolen voor macrosymbool
        index = (bi2de(source(((i-1)*aantal_bron_symbolen)+1:aantal_bron_symbolen*i)))+1; %Bepaal hashvalue horende bij macrosymbool om onze freq_tabel mee
                                                                                          % te indexeren          
        freq_tabel(index) = freq_tabel(index)+1; %Verhoog bijhorende freq met 1
    end
    
    %converteer
    for j=1:2^aantal_bron_symbolen,
        freq_tabel(j) = freq_tabel(j)/i;
    end
    
    huffman_dict = huffmandict(alphabet, freq_tabel);
   
    