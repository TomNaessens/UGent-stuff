%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%          VRAAG 4         %
%     Kanaalcodering       %
% Product code opstellen   %
% Sander Demeester         %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
clear

%Als test is dit de (6,3) - code. Omdat de ham_encode nog niet klaar is
%moet in mijn code hiermee testen.
encodeertabel = [0 0 0 0 0 0 0 0 0 ; 0 0 1 0 0 1 1 0 0 ; 0 1 0 0 1 0 1 1 0 ; 0 1 1 0 1 1 0 1 0 ; 1 0 0 1 0 0 1 1 1 ; 1 0 1 1 0 1 0 1 1 ; 1 1 0 1 1 0 0 0 1 ; 1 1 1 1 1 1 1 0 1 ];
informatiewoorden = encodeertabel(1:end,1:3);
codewoorden = encodeertabel(1:end,4:end);

l = 2;
[i,j] = size(codewoorden);
b = 0;
s = 1;
a = [];
output = [];
for k=1:i/l,
    p_m = codewoorden((s):(s),1:end);
    for h=2:l
        h + b;
        p_m = vertcat(p_m,codewoorden((h+b):(h+b),1:end)); %concat van informatiecooden uit codewoorden. 
        
    end
    b = (b + l); %offset berekening voor (alles)-eerste vector.
    s = (s + l);   %offset berekening voor eerste vector
    
    [i2,j2] = size(p_m); %bepaal dementie van matrix pariteitcode
    p_m; % Dit zijn de l*k zonder pariteit bit
    for k1=1:j2,
       a = horzcat(a, mod(sum(p_m(1:end,k1:k1)),2));  %bepaal pariteit bit
    end
    p_m = [p_m;a]; %dit is de (l+1)*n (die we volgens de opgave rij per rij gaan versturen) 
    output = [output;p_m];
    p_m
    % In de praktijk zal dit gewoon 1 lange string zijn. die dan in de
    % volgende opgave zal worden opgeplist in l+1 delen.
    a = [];
end
output(:);


