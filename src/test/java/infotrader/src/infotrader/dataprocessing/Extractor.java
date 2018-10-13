/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package infotrader.src.infotrader.dataprocessing;

import infotrader.src.infotrader.datamodel.DocumentI;

/**
 *
 * @author user
 */
public abstract class Extractor {
    
        DocumentI doc;
    
    public Extractor(DocumentI doc){
    
        this.doc = doc;
    
    }
    
    public abstract void extract(String doc);
}
