%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%          VRAAG 3          %
%     Kanaalcodering        %
%     Sander Demeester      %
% Encoderen van hammingcode %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clear
n = 15; % Aantal codebits
k = 11; % Aanminertal informatie bits (aantal echte databits te we mappen op codebits)

% Laden van bitsrc
load('Xfile4.mat');

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

[~,number_of_bits] = size(bitsrc);

% Om onze informatiebits om te zetten naar codebits maken we gebruik van
% een linaire transformatie (zoals beschreven op pagina 41).
% Omdat we een (15,11) code hebben hebben we dus een veelvoud van 11 nodig
% om een linaire transformatie te hebben.


bitsrc = horzcat(bitsrc, zeros(1,mod(k-number_of_bits,k)));

% Ha! blijkt daar een mooie box te staan met handige matlab functies :)
bitsrc = reshape(bitsrc,k,[])';

% Het encoderen zelf.
bitenc = mod( bitsrc * sys_generator,2);
