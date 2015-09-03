function performance = feedforward()
%% Reading and normalizing the data
m = 10;                   % Maximum number of neurons
diabetes = dlmread('pima-indians-diabetes_data.txt',',');   % Read the database
P = diabetes(:,1:end-1)'; % Input data
T = diabetes(:,end)';     % Target data
[PN,PS] = mapstd(P);      % Normalizing mean and standard deviation to 0 and 1 row-wise
% PN transformed data, PS settings containing
% means and variances.
%% Rearranging data randomly
p = randperm(length(T));
PN = PN(:,p);
T = T(:,p);

performance = zeros(1,m);
for n = 2:m
    n
    %% Creating the neural network with 2 hidden layers
    net = newff(PN,T,[n,n],{'tansig','tansig','tansig'},'traingd');
    %% Setting the parameters of the network
    net.divideFcn = 'divideblock';
    net.divideParam.trainRatio = 0.4;
    net.divideParam.valRatio = 0.3;
    net.divideParam.testRatio = 0.3;
    net.trainParam.show = 5;
    net.trainParam.max_fail = 5;
    net.trainParam.epochs = 1000;
    net.trainParam.min_grad = 0;
    net.trainParam.lr = 0.01;
    net.trainParam.showWindow = false;
    %% Getting the minimum performance out of 5 trials with the same network
    for t = 1:5
        net = init(net);
        [net,tr] = train(net,PN,T);
        %perf = tr.tperf(tr.best_epoch);
        perf = tr.best_tperf;
        if t == 1
            performance(n) = perf;
        elseif perf < performance(n)
            performance(n) = perf;
        end
    end
end
performance(1) = performance(2);
figure
plot(performance)