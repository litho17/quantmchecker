/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package smartmail.process.controller.module;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;
import smartmail.logging.module.ObjSerializer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import org.apache.hadoop.io.BytesWritable;
import org.apache.hadoop.io.Writable;
import smartmail.datamodel.EmailEvent;
import smartmail.datamodel.MessageWord;

/**
 *
 * @author user
 */
public class Partitioner {

    List<List<BytesWritable>> sfmaplist;
    private final int partitionsize;
    StateHolder sfile;

    public Partitioner(int psize, StateHolder sfile) {
        partitionsize = psize;
        this.sfile = sfile;
        initseqfiles();
    }

    private void initseqfiles() {

        @Bound("sfile.sfmap") int i;
        @Inv("= (- valuesl it) (- c46 c45)") List<BytesWritable> valuesl = new ArrayList();
        @Iter("<= it sfile.sfmap") Iterator<BytesWritable> it = sfile.sfmap.values().iterator();
        while (it.hasNext()) {
            BytesWritable bw;
            c45: bw = it.next();
            c46: valuesl.add(bw);
        }
        sfmaplist = chopped(valuesl, partitionsize);

    }

    static List<List<BytesWritable>> chopped(List<BytesWritable> list, final int L) {
        @Bound("list") int j;
        //STAC: The list partitioner function
        @Inv("= (- parts i) (- c53 (* L c56))") List<List<BytesWritable>> parts = new ArrayList<List<BytesWritable>>();
        final int N = list.size();
        for (@Iter("(and (<= i list) (<= 1 L))") int i = 0; i < N; ) {
            c53: parts.add(new ArrayList<BytesWritable>(
                    list.subList(i, Math.min(N, i + L)))
            );
            c56: i = i + L;
        }
        return parts;
    }

    List<BytesWritable> getPartition(int i) {
        //BytesWritable next = itrtr.next();
        //MessageWord deobj = (MessageWord) ObjSerializer.deSerializeObj(next);

        return sfmaplist.get(i);
    }
}
