p = [0.3 0.1 0.03 0.01 0.003 0.001];
a_decodeerfoutkans = [0.964732 0.450957 0.0729725 0.00962977 0.000920759 0.000104094];
a_decodeerfoutkans_p = [1 0.99174 0.45468 0.074491 0.0073424 0.00083245];
a_decodeerfoutkans_p = a_decodeerfoutkans_p/8;

waarden_x_as=p;

loglog(waarden_x_as, a_decodeerfoutkans_p, '-bo', waarden_x_as, a_decodeerfoutkans, '-ro');
title('Opgave 3.2.6: Decodeerfout ten opzichte van foutprobabiliteit');
ylabel('Decodeerfout');
xlabel('Foutprobabiliteit');
leg1 = legend('Analytische Productcode', 'Analytische Hammingcode');
set(leg1,'Location','NorthWest')