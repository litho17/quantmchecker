package com.cyberpointllc.stac.host;

import com.cyberpointllc.stac.textcrunchr.OutputHandler;
import com.cyberpointllc.stac.textcrunchr.TextFileHandler;
import com.cyberpointllc.stac.textcrunchr.WindowOutputHandler;
import plv.colorado.edu.quantmchecker.qual.ListInv;

import java.io.File;

/**
 * @author Tianhan Lu
 */
public class Driver {
    public static void main(String[] args) throws Exception {
        while(true) {
            @ListInv({"<self>.results+rem(???)=-TextFileHandler.c32+OutputHandler.c41/c44", "<self>.namesToPaths+rem(results)=OutputHandler.c50-OutputHandler.c49"}) OutputHandler outputHandler = new WindowOutputHandler();
            TextFileHandler tfHandler = new  TextFileHandler();
            tfHandler.processFile("filename", outputHandler, args);
            outputHandler.conclude();
        }
    }
}
