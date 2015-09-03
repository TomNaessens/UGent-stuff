p = [0.3 0.1 0.03 0.01 0.003 0.001];
a_decodeerfoutkans = [0.964732 0.450957 0.0729725 0.00962977 0.000920759 0.000104094];
g_decodeerfoutkans = [0.9641 0.4489 0.0733 0.0102 0.0008 .0001];

waarden_x_as=p;

loglog(waarden_x_as,g_decodeerfoutkans, '-ro', waarden_x_as,a_decodeerfoutkans, '-bo');
title('Opgave 3.2.3: Decodeerfout ten opzichte van foutprobabiliteit');
ylabel('Decodeerfout');
xlabel('Foutprobabiliteit');
leg1 = legend('Gevonden', 'Analytische');
set(leg1,'Location','NorthWest')