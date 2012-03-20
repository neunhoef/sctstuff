



pubcrawl_linearprog' :: CrawlCoefficients -> (Double,[Double])
pubcrawl_linearprog' dss = let {
        l = V.length $ V.head dss ; 
        p = Minimize $ 1 : replicate l 0 ; 
        row = map fromInteger . V.toList ;
        cs = Dense $ ((0 : replicate l 1) :<=: 1) 
                : map (\x -> [(-1 : row x) :<=: 0]) dss 
    } in case  simplex p cs [ 1 :<=: 0 ]  of 
           Optimal (epsi,epsi0:coeffs) -> assert (epsi==epsi0) (epsi,coeffs)
           x -> error $ "pubcrawl_linearprog found " ++ show r 

pubcrawl_linearprog :: CrawlCoefficients -> (Int,CrawlCoefficients)
pubcrawl_linearprog dss = let {
        (epsilon,coeffs) = pubcrawl_linearprog' dss ;
        m = maximum $ map (V.maximum . map abs) dss ;
        d = abs epsilon / fromInteger (5*l*m) ; 
   } in ( ceiling $ epsilon/d ,
          V.fromList $ map (\v -> round $ v/d) coeffs )




        m = V.map (\i -> maximum $ map (abs . (! i)) dss) [1..l] ; 
