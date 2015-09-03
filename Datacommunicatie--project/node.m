classdef node
    properties
        value;
        freq;
        left;
        right;
        is_leaf;
    end
    
    methods
       
        % Overloading van de sorteerfunctie zodat we sort() kunnen
        % gebruiken om de array van nodes te sorteren.
        function [obj,idx]=sort(obj)

            [~,idx]=sort([obj.freq],'descend'); 
            obj=obj(idx);

        end
    end
end