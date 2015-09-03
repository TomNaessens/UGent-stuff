%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%          VRAAG 1         %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

[A] = imread('alberteinstein.bmp','bmp'); % Leest een image in in een 2-dimens. array, geen [A,B] want de colourmap hebben we niet nodig
[row, col] = size(A);

Y = mat2cell(A, repmat(2,[1 size(A,1)/2]), repmat(2,[1 size(A,2)/2]));

macro_symbols_abs_freq = zeros(16,1);
alphabet = 1:16;
    

for i=1:(row*col/4),
    index = Y{i}(1)*8+Y{i}(2)*4+Y{i}(3)*2+Y{i}(4)+1; % Wit is 0
                                                     % 1 3
                                                     % 2 4
    macro_symbols_abs_freq(index) = macro_symbols_abs_freq(index) + 1;
end

format long
% Het is hier niet nodig een for loop over elk element te doen: zo kunnen 
% we het ook:
macro_symbols_rel_freq = macro_symbols_abs_freq/i


Source_Coding.create_codebook(alphabet, macro_symbols_rel_freq);

% macro_symbols =
%        12478
%          193
%          172
%          227
%          168
%          235
%           18
%          147
%          194
%            8
%          269
%          157
%          175
%           99
%          173
%        15887

