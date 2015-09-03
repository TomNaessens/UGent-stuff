% Load the database and split the dataset in patterns P and target values T
diabetes = dlmread('pima-indians-diabetes_data.txt',','); %data
P = diabetes(:,1:end-1)';%patterns
T = diabetes(:,end)';% targets

% Normalize the input P
%[PN, PS] = mapstd(P);

% Divide the normalized data into a training, validation and test set
[TRN, VAL, TST] = dividevec (P, T, 0.15, 0.15); % split data
T
% Create auxiliary variables
P1 = TRN.P;
T1 = TRN.T;
P2 = VAL.P;
T2 = VAL.T;
P3 = TST.P;
T3 = TST.T;

%% 

% Compare histograms of T1, T2 and T3
figure
hist (T1)
xlabel('targets')
ylabel('Frequency')
title('Histogram of targets (Training set)')

%% 

figure
hist (T2)
xlabel('targets')
ylabel('Frequency')
title('Histogram of targets (Validation set)')
%% 

figure
hist (T3)
xlabel('targets')
ylabel('Frequency')
title('Histogram of targets (Test set)')

%%

figure
[A1, bin1] = hist (P1(1, :));% histogram of attribute 1 in the training set 
[A2, bin2] = hist (P2(1, :));% histogram of attribute 1 in the validation set 
[A3, bin3] = hist (P3(1, :));% histogram of attribute 1 in the test set

plot (bin1, A1, bin2, A2, bin3, A3)
xlabel('Attribute 1')
ylabel('Frequency')
title('Distribution of attribute 1 without normalization') 
legend('Training set','Validation set','Test set')
grid
