function bitdec = SProd_decode(bitenc)
            bitenc = bitenc(:)';    % zorg ervoor dat de input een rijvector is
            N = length(bitenc);
            N_codewords = N/15/(8+1);
            
            if(mod(N, 15*(8+1)) ~= 0)
                error('input is geen geheel aantal codewoorden.');
            end
            
            bitenc = reshape(bitenc,[],15);
            size(bitenc)
            
            output = [];
            
            stop = 9;
            
            for i=1:size(bitenc,1),
                if i ~= stop
                    output = [ output bitenc(i,:) ];
                elseif i == stop
                    stop = stop+9;
                end
            end
            
            bitdec = output;
            

end
