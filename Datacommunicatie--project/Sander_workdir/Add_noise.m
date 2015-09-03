function dataWithNoise = Add_noise(dataWithoutNoise,noiseChance)
            
        for i=1:numel(dataWithoutNoise),
                
                if(rand(1) < noiseChance)
                    
                    dataWithNoise(i) = mod(( dataWithoutNoise(i) + 1),2); 
                
                else
                
                    dataWithNoise(i) = dataWithoutNoise(i);
                    
                end        
        end
end     


% albertingelezen=imread('alberteinstein.bmp')
% albert1noise=Add_noise(albertingelezen,0.01)
% albert1noisereshaped=reshape(albert1noise,400,306)
% imwrite(~albert1noisereshaped,'oef7afbeeld1.bmp')

% albertingelezen=imread('alberteinstein.bmp')
% albert1noise=Add_noise(albertingelezen,0.01)
% albert1noisereshaped=reshape(albert1noise,400,306)
% imwrite(~albert1noisereshaped,'oef7afbeeld1.bmp')