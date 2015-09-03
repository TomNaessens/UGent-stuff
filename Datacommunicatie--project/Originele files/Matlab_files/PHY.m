classdef PHY_full
          
   methods(Static=true)
        
        %% Functies voor Mapping/Demapping
        function a = mapper(bitstring, constellation)
            % Functie die een bitstring mapped naar complexe symbolen.
            % input:
            % bitstring: vector van ongecodeerde bits met lengte 1xN
            % constellation: ofwel 'BPSK', '4QAM', 'QPSK', '4PAM', ...
            % output: vector met (complexe) symbolen 
            
                       
            switch(constellation)
                case 'BPSK'                    
                    % BPSK mapping here
                    
                    a = (bitstring-1/2)*2;                                                  
                    
                case 'D-4PSK'                  
                    
                    % map differentieel geencodeerde 4-PSK hier
                    
                otherwise
                    error('Constellation not recognized');
            end
                        
        end        
        function bitstring = demapper(a, constellation)
            % Functie die complexe symbolen omzet naar bits
            % input:
            % a: vector met (complexe symbolen)
            % constellation: ofwel 'BPSK', 'QAM', 'QPSK', '4PAM', etc    
            
            switch(constellation)
                case 'BPSK'                       
                    bitstring = (a+1)/2;   
                    
                case 'D-4PSK'
                    
                   % demap differentieel geencodeerde 4-PSK hier
                    
                otherwise
                    error('Constellation not recognized');
            end
        end        
        function a_estim = harddecisions(x, constellation)
            % Functie die harde desicie toepast op x
            % input:
            % x: vector met ruizige (complexe) symbolen
            % constellation ofwel 'BPSK', '4QAM', 'QPSK', '4PAM', etc   
            
            switch(constellation)
                case 'BPSK'                   
                     
                    a_estim(x<0) = -1;
                    a_estim(x>0) = 1;                   
                
                    
                case 'D-4PSK'                    
                    
                    % harde decisie voor differentieel geencodeerde 4-PSK hier
                    
                otherwise
                    error('Constellation not recognized');
                    
            end
                
                
        end
        
        %% moduleren/demoduleren
        function s = modulate(a,T,Ns,frequency,alpha,Lf)
            % Zet een vector symbolen op puls en moduleert dit signaal op een golf
            % input:
            % a = vector of symbols
            % T = symbol duration
            % Ns = samples per symbol
            % frequency = carrier frequency
            % alpha = roll-off factor
            % Lf = pulse duration (in samples)
            % s = vector containing samples of modulated signal
            
            
            % vul aan
            
        end        
        function rdemod = demodulate(r,T,Ns,frequency,alpha,Lf)
            % Demoduleert het signaal r en voert het matched filter uit. 
            % input:
            % r: vector of received signal samples
            % T: symbol duration
            % Ns: samples per symbol
            % frequency: carrier frequency
            % alpha: roll-off factor
            % Lf: pulse duration
            %
            % output y: vector of demodulated samples
            
            % vul aan
            
        end        
        function y = pulse(t,T,alpha)
            % Functie: De square root raised cosine pulse
            % input:
            % t sample waarden
            % T tijdsinterval van 1 symbool: standaard gelijk aan 1
            % alpha: rolloff factor
            % vb van gebruik
            %
            % alpha = 0.5;
            % t = [-5:0.1:5];
            % s = PHY.pulse(t, 1, alpha);
            % plot(t, s)
            % xlabel('tijd t/T');
            % ylabel('y(t)');
            % title(['Square root raised cosine pulse met rollofffactor ' num2str(alpha)]);
                        
            een=(1-alpha)*sinc(t*(1-alpha)/T);
            twee=(alpha)*cos(pi*(t/T-0.25)).*sinc(alpha*t/T-0.25);
            drie=(alpha)*cos(pi*(t/T+0.25)).*sinc(alpha*t/T+0.25);
            y=1/(sqrt(T))*(een+twee+drie);

        end
        
        function y=downSample(x,Ns,Lf)
            % Functie die het gegeven signaal downsampled
            % input:
            % x: vector met samples
            % Ns: samples per symbool
            % Lf: pulse duration
            % output: rijvector met 1 sample per symbool
        end   
        
        %% het kanaal
        function r = channel_AWGN(s, Ns, sigma)
            % Functie die een AWGN kanaal simuleert
            % input:
            % s: rijvector met samples van het signaal
            % Ns: samples per symbol
            % sigma: standaard deviatie van de ruis.
        end
        
        function r = channel_phaseNoise(s, Ns, sigma, faseNoiseStd)
            % Functie die een kanaal simuleert waarbij de
            % draaggolfoscillator van de ontvanger onderhevig is aan
            % fasefluctuaties ('faseruis').
            % input:
            % s: rijvector met samples van het signaal
            % Ns: samples per symbol
            % sigma: standaard deviatie van de ruis.
            % faseNoiseStd: standaard deviatie van het faseincrement voor één symboolperiode
            
            N = length(s);            
            n_theta = zeros(1, N);
            for k=1:N
                n_theta(k) = n_theta(k-1) + faseNoiseStd/sqrt(Ns)*randn();    
            end
            
            % voeg nog steeds AWGN toe
            r = PHY.channel_AWGN(s, Ns, sigma);
        end      
        
        
    end
    
end