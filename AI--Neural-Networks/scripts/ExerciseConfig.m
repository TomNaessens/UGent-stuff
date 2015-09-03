function ExerciseConfig()

mySeed = 2342;

rng(mySeed);            % seeds the random number generator using the non-negative integer mySeed
%% Reading and normalizing the data
diabetes = dlmread('pima-indians-diabetes_data.txt',',');   % Read the database
P = diabetes(:,1:end-1)'; % Input data
T = diabetes(:,end)';     % Target data
[PN,PS] = mapstd(P);      % Normalizing mean and standard deviation to 0 and 1 row-wise
                          % PN transformed data, PS settings containing
                          % means and variances.
                          %% Configuring and training the network
Nnodes = 10;           % Number of nodes
lr = 0.005;            % Learning rate 
epochs = 1000;         % Iterations
frac = 0.95;            % Percentage of the database devoted for validation and test
show = 5;
k = 0.001;               % Controls the variance of the weights
 M = k*randn(Nnodes,8);  % Initialization of the weighting matrix of the hidden layer
b1 = k*randn(Nnodes,1);  % Initialization of the bias of the hidden layer 
b2 = k*randn(1,1);       % Initialization of the bias of the output layer

%% Splitting the dataset into Training (TRN) Validation (VAL) and Test
%% (TST)
[TRN,VAL,TST]=dividevec(PN,T,frac/2,frac/2);
%load('TRN.mat')
%load('VAL.mat')
%load('TST.mat')

%% Training the Neural Network
[net,tr] = SingleHiddenLayerNetwork(Nnodes,lr,epochs,show,TRN,VAL,TST,M,b1,b2);

end

function [net,tr] = SingleHiddenLayerNetwork(Nnodes,lr,epochs,show,TRN,VAL,TST,M,b1,b2)

%% Create a feedforward network with 2 layers and 'Nnodes' hidden nodes
net = newff(minmax(TRN.P),[Nnodes,1],{'logsig','purelin'},'traingd');

%% Set training parameters
net.trainParam.epochs = epochs;
net.trainParam.min_grad = 0;    % Allow gradient to approach zero
net.trainParam.lr = lr;         % Use a small learning rate
net.trainParam.show = show;
net.trainParam.max_fail = epochs;
net.trainParam.goal = 0;
net.performFcn = 'mse';         % Evaluation metric
net.plotFcns = {'plotperform', 'plottrainstate', 'ploterrhist', 'plotconfusion', 'plotroc'}

%% Train the network
% Set the initialization weights
net.iw{1,1}= M;
net.b{1,1} = b1;
net.b{2,1} = b2;
% Display the initial weights
net.iw{1,1}
net.b{1,1}
net.b{2,1}
% Training
[net,tr] = train(net,TRN.P,TRN.T,[],[],VAL,TST);
% Network weights after training
net.iw{1,1}
net.b{1,1}
net.b{2,1}

end