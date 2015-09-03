%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%          VRAAG 3         %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
clear;
[A] = imread('alberteinstein.bmp','bmp'); % Leest een image in in een 2-dimens. array, geen [A,B] want de colourmap hebben we niet nodig
[row, col] = size(A);

Y = mat2cell(A, repmat(2,[1 size(A,1)/2]), repmat(2,[1 size(A,2)/2]));

macro_symbols_abs_freq = zeros(16,1);
bitsrc = zeros(1,(row*col/4));
alphabet = 1:16;

for i=1:(row*col/4),
    index = Y{i}(1)*8+Y{i}(2)*4+Y{i}(3)*2+Y{i}(4)+1; % Wit is 0
                                                     % 1 3
                                                     % 2 4
    bitsrc(i) = index;
    macro_symbols_abs_freq(index) = macro_symbols_abs_freq(index) + 1;
end

format long
% Het is hier niet nodig een for loop over elk element te doen: zo kunnen 
% we het ook:
rel_freq = macro_symbols_abs_freq/i;


codewords = Source_Coding.create_codebook(alphabet, rel_freq);

% Afbeelding 1: idem als 7i

% Afbeelding 2: gecomprimeerde transmissie
huff_encoded = Source_Coding.Huffman_encode(bitsrc, alphabet, codewords);
afb2_noice = Add_noise(huff_encoded,0.02);
huff_decoded = Source_Coding.Huffman_decode(afb2_noice, alphabet, codewords);
huff_decoded = [huff_decoded ones(1, size(bitsrc,2)-size(huff_decoded,2))];
decoded_matrix = reshape(huff_decoded,200,153);


for i=1:row/2,
    for j=1:col/2,
        image_matrix{i, j} = reshape(de2bi(decoded_matrix(i, j)-1, 4, 'left-msb'), 2, 2);
    end
end

decoded_matrix = cell2mat(image_matrix);

imwrite(~decoded_matrix,'3_2.bmp');

% Afbeelding 3: gecomprimeerde & gecodeerde transmissie transmissie
% Aangezien de prod_decode niet is afgeraakt kunnen we deze niet opstellen.