//*****************************************************************************
//   File:         main.cxx
//
//   Description:  Main used to test the text classifier object.
//
//   Author:        Robert A. Murphy
//   Date:          Jan. 29, 2015
//*****************************************************************************/

import java.io.*;
import java.util.*;

class FDATA {
    int [] row      = null;
    int [][] cls    = null;
    String [][] nda = null;
    double [][] mns = null;
    double B;
    double len;
}

public final class DataClassification extends Thread implements Runnable {

    protected static double N;
    protected static double N_SQR;
    protected static double M;
    protected static double M_SQR;
    protected static double RATE;
    protected static double MRATE;
       
    protected static int ROWS;
    protected static int COLS;
    protected static int S_ROWS;
    protected static int P_ROWS;
    protected static int ERRORS;
    protected static int COUNT;
    protected static int MAX_INST;
    
    protected int inst;
    
    protected static int [] srows   = null;
    protected static int [] prows   = null;
    protected static int [] poprows = null;
    protected static int [] status  = null;
    protected static int [] errvar  = null;
    
    @SuppressWarnings("VolatileArrayField")
    protected static volatile int [][] clusters = null;
    protected static int [][] ncrows   = null;

    protected static double S;
    protected static double B;
    protected static double L;
    protected static double variance;

    protected static double [][] data   = null;
    @SuppressWarnings("VolatileArrayField")
    protected static volatile double [][] means  = null;
    protected static double [][] nmeans = null;
    
    protected static HashMap hash;
    
    protected static boolean pm;
    
    protected static String [][] odata = null;
    protected static String [][] cdata = null;
    protected static String [][] adata = null;
    
    protected static final String [] arr = {"",
                                            "\"",
                                            "#",
                                            "'",
                                            "(",
                                            ")",
                                            "*",
                                            "+",
                                            ",",
                                            "-",
                                            ".",
                                            "0",
                                            "1",
                                            "2",
                                            "3",
                                            "4",
                                            "5",
                                            "6",
                                            "7",
                                            "8",
                                            "9",
                                            "<",
                                            "?",
                                            "@",
                                            "a",
                                            "b",
                                            "c",
                                            "d",
                                            "e",
                                            "f",
                                            "g",
                                            "h",
                                            "i",
                                            "j",
                                            "k",
                                            "l",
                                            "m",
                                            "n",
                                            "o",
                                            "p",
                                            "q",
                                            "r",
                                            "s",
                                            "t",
                                            "u",
                                            "v",
                                            "w",
                                            "x",
                                            "y",
                                            "z"};
    
    protected static final double e = Math.E;
    
    protected static final int FILLER_VALUE = -1;
    
    protected static final String DEFAULT_BLOCK_SIZE = "500";
    
    protected static final boolean DEFAULT_DYNAMIC_THREADS = false;
    
    protected static final boolean DEFAULT_THREAD_LOGGING = true;
    
    public DataClassification() { inst = FILLER_VALUE; }
    
    public DataClassification( int instance ) {
        // set the instance arguments for later usage
        inst = instance;
    }
    
    public DataClassification( HashMap args, boolean patternmatch ) {

        int row;
        int col;
        int val;
        int block;
        int dfbs = DEFAULT_BLOCK_SIZE != null          ?
                   Integer.valueOf(DEFAULT_BLOCK_SIZE) :
                   1000;

        String       th = null;
        String       ct = null;
        String       mr = null;
        String       bs = null;
        String []    co = null;
        String [][]  cl = null;
        String [][]  da = null;

        double CRATE = 0.0;

        boolean dt = th != null && th.compareTo("1") == 0 ?
                     true                                 :
                     DEFAULT_DYNAMIC_THREADS;

        // set the instance arguments for later usage
        hash = args;
        pm   = patternmatch;
        inst = 0;

        /*
         * get the number of classes, if defined
         * get the columns to be classified
         * get the classes to be defined
         * get the data
         * all of it from the hashmap passed by the gui
         */
        ct = (String)args.get("COUNT");
        mr = (String)args.get("MRATE");
        co = (String[])args.get("COLUMNS");
        cl = (String[][])args.get("SUBSETS");
        da = (String[][])args.get("DATA");

        /*
         * condition the data in da by replacing the strings with
         * numeric representations from arr
         */
        condition(co,cl,da);

        /*
         * after data conditioning, we are now in a
         * position to assign values to the class
         * data members
         */
        ROWS     = da.length;
        COLS     = da[0].length;
        N_SQR    = ct != null ? Double.valueOf(ct).doubleValue() : count2();
        N        = Math.sqrt(N_SQR);
        if( dt ) {
            MAX_INST = (int)Math.ceil(N);
        }
        else {
            block    = bs != null                     ?
                       Integer.valueOf(bs).intValue() :
                       dfbs;
            val      = block / dfbs;
            MAX_INST = val <= 0 ? 1 : val;
        }

        // yes, both lines are required for MRATE
        MRATE    = mr != null ? Double.valueOf(mr).doubleValue() : 0.5;
        MRATE    = 0.0 <= MRATE && MRATE <= 1.0 ? MRATE : 0.5;
        CRATE    = MRATE / (1.0 - MRATE);

        //M        = Math.ceil((N + Math.sqrt((2.0 * N_SQR) - (2.0 * N) + 1.0)));
        M        = -(CRATE * N) + Math.sqrt( (CRATE * Math.pow(N-1.0,2.0)) + Math.pow(CRATE*N,2.0) );
        M_SQR    = Math.pow(M,2.0);
        S_ROWS   = (int)Math.ceil(N_SQR);
        P_ROWS   = (ROWS - S_ROWS);
        S        = (M_SQR + Math.pow((N - 1.0),2.0) + (2.0 * M * N));
        B        = 1.0/Math.sqrt(S);
        L        = ((double)ROWS)/M_SQR;
        ERRORS   = 0;
        COUNT    = 0;
        RATE     = 2.0;

        variance = 0.0;

        srows   = new int[S_ROWS];
        prows   = null;
        poprows = null;

        // memory for the thread status other than the 0 inst
        status = new int[MAX_INST-1];

        clusters = new int[ROWS][ROWS];

        means = new double[ROWS][COLS];
        data  = new double[ROWS][COLS];

        // change the data array of strings to doubles
        for( row = 0; row < data.length; row++ ) {
            for( col = 0; col < data[0].length; col++ ) {
                data[row][col] = Double.valueOf(da[row][col].trim()).doubleValue();
            }
        }

        // initialize the cluster rows and cols
        for( row = 0; row < clusters.length; row++ ) {
            Arrays.fill(clusters[row],FILLER_VALUE);
        }

        /* sample from the input data array
         * according to the Poisson distribution
         * and get the rest of the population
         */
        samples(cl);
    }
    
    public void run() {

        String nm = null;
        String stl = System.getenv("THREAD_LOGGING");

        boolean tl = stl != null && stl.compareTo("1") == 0 ?
                     true                                   :
                     DEFAULT_THREAD_LOGGING;

        // start classify with the proper arguments
        try {
            classify();
        }
        catch( IOException ioe ) {
            System.out.println( "classify() - " + ioe.getMessage() );
        }

        if( tl ) {
            try {
                nm = "mainclusters.out";
                logwriter(nm,clusters,odata);
            }
            catch( IOException ioe ) {
                System.out.println( nm + " - " + ioe.getMessage() );
            }        
            // log the clusters and means
            try {
                nm = "clusters.out";
                logwriter(nm,clusters);
            }
            catch( IOException ioe ) {
                System.out.println( nm + " - " + ioe.getMessage() );
            }
            // log the samples and remaining population
            try {
                nm = "samples.out";
                logwriter(nm,srows);
            }
            catch( IOException ioe ) {
                System.out.println( nm + " - " + ioe.getMessage() );
            }
            try {
                nm = "population.out";
                logwriter("population.out",prows);
            }
            catch( IOException ioe ) {
                System.out.println( nm + " - " + ioe.getMessage() );
            }
        }

        return;
    }
    
    public static void main2( String [] args ) throws FileNotFoundException, IOException {

        int col;
        int row;
        int rows = 0;
        int ctok = 1;
        int tok  = 0;
        int clen = 1;
        int len  = 0;
        int rbs;
        int bs;
        int b;
        int i;
        int j;
        int r;
        int cmax = 1;
        int rmax = 0;
        int mmax = 1;
        int val;
        int frow;
        int trow;

        double dist;

        File fstream;

        RandomAccessFile in;

        String strLine;
        String token;
        String nm    = null;
        String block = null;

        String [] tokens = null;

        String [][] oda = null;
        String [][] cda = null;

        DataClassification dc = new DataClassification();

        HashMap [] h = null;

        FDATA [] fd = null;

        boolean bfound = false;

        // get the block size
        bs = block != null                                 ?
             Integer.valueOf(block).intValue()             :
             Integer.valueOf(DEFAULT_BLOCK_SIZE).intValue();

        /*
         * open the data file and read the data into a 2-d array
         */

        // Open the file
        fstream = new File(args[0].trim());

        // Get the object of DataInputStream
        in = new RandomAccessFile(fstream,"r");

        // first count the number of lines in the file
        while( (strLine = in.readLine()) != null ) {
            rows++;
            tokens = strLine.split( "\\|" );
            ctok   = tokens.length;
            if( ctok > tok ) {
                tok = ctok;
            }
            else {
                // keep the current length as the max
            }
            clen   = tokens[0].length();
            if( clen > len ) {
                len = clen;
            }
            else {
                // keep the current length as the max
            }
        }

        // number of errors encountered for each row of data
        errvar  = new int[rows];

        // rewind the file to the beginning position
        in.seek(0);

        // count the number of blocks
        rbs = rows % bs;
        b   = rbs == 0 ? rows / bs : (rows / bs) + 1;

        // memory for the original data
        oda = new String[rows][tok];

        // create some HashMaps for the returns
        h = new HashMap[b];

        // memory to hold the data in each iteration
        fd = new FDATA[b];

        try {
            row = 0;
            while( (strLine = in.readLine()) != null ) {
                tokens = strLine.split( "\\|" );
                // get the new row ... note that row = rows at this point
                for( col = 0;
                    (row < oda.length) && (col < oda[row].length);
                     col++ ) {
                    token         = tokens[col].trim();
                    oda[row][col] = token != null ? token : "";
                }
                row++;
            }
        }
        catch( EOFException eofe ) {
            // end of file ... just break
            System.out.println(eofe.getMessage() + "Reading of file completed.....");
        }
    
        // set odata to oda for later usage
        odata = oda;

        // close the input file
        in.close();
        System.out.println("Reading of file completed.....");

        // characterize the data before classifying
        cda = dc.characterize(oda);

        // assign numeric representations to the characters in arr
        adata = dc.assign( arr );

        // Read File Line By Line
        for( i = 1; i <= b; i++ ) {
            // make sure we capture the data for later use
            fd[i-1] = new FDATA();
            if( fd[i-1].nda == null ) {
                // starting with the initial block
                if( i == b ) {
                    if( rbs != 0 ) {
                        // rows is not a full block
                        fd[i-1].nda = new String[rbs][len];
                    }
                    else {
                        // rows is a full block
                        fd[i-1].nda = new String[bs][len];
                    }
                }
                else {
                    // size nda as a full block initially
                    fd[i-1].nda = new String[bs][len];
                }
            }
            else {
                if( i == b ) {
                    if( rbs != 0 ) {
                        // resize nda for the last rows
                        fd[i-1].nda = new String[rbs][len];
                    }
                    else {
                        // keep the same nda with bs rows
                    }
                }
                else {
                    // keep the same nda with bs rows
                }
            }
            for( row = 0; row < Math.min(fd[i-1].nda.length,cda.length); row++ ) {
                for( col = 0; col < Math.min(fd[i-1].nda[0].length,cda[0].length); col++ ) {
                    fd[i-1].nda[row][col] = cda[row+((i-1)*bs)][col];
                }
                /*
                 * fill nda with the null string if the length
                 * in cda doesn't match what's in nda
                 */
                if( cda[0].length < fd[i-1].nda[0].length ) {
                    for( col = cda[0].length; col < fd[i-1].nda[0].length; col++ ) {
                        fd[i-1].nda[row][col] = "";
                    }
                }
                else {
                    // we're all good here
                }
            }
            // driver does the main bit of processing
            h[i-1] = dc.driver(fd[i-1].nda);
            // get the current clusters and means
            fd[i-1].cls = (int[][])h[i-1].get("CLUSTERS");
            fd[i-1].mns = (double[][])h[i-1].get("MEANS");
            // count the number of clusters for getting memory
            for( frow = 0;
                (frow < fd[i-1].cls.length) && (fd[i-1].cls[frow][0] != FILLER_VALUE);
                 frow++ ) {
                // when the loop breaks we will have a count of the clusters
            }
            fd[i-1].row = new int[frow];
            // get the upper bound on the distance
            fd[i-1].B = B;
            // continue calculating the max values
            val   = dc.rowmax(fd[i-1].cls);
            rmax += val;
            // continue calculating the max values
            val = dc.colmax(fd[i-1].cls);
            if( val > cmax ) {
                cmax = val;
            }
            else {
                // keep the current row max
            }
            val = fd[i-1].mns[0].length;
            if( val > mmax ) {
                mmax = val;
            }
            else {
                // keep the current max number of cols in the means array
            }
        }

        // get memory for the amalgamated clusters and means
        clusters = new int[rmax][b*cmax];

        // initialize the memory with FILLER_VALUE
        for( row = 0; row < clusters.length; row++ ) {
            for( col = 0; col < clusters[0].length; col++ ) {
                clusters[row][col] = FILLER_VALUE;
            }
        }

        // amalgamate the clusters
        for( i = 0; i < b; i++ ) {
            //start by adding the first block to clusters
            if( i == 0 ) {
                for( row = 0;
                    (row < Math.min(fd[i].row.length,fd[i].cls.length)) &&
                    (fd[i].cls[row][0] != FILLER_VALUE);
                     row++ ) {
                    for( col = 0;
                        (col < fd[i].cls[row].length) && (fd[i].cls[row][col] != FILLER_VALUE);
                         col++ ) {
                        clusters[row][col] = fd[i].cls[row][col];
                    }
                    fd[i].row[row] = row;
                }
            }
            else {
                /*
                 * add any subsequent blocks by taking the current one
                 * in the list and comparing it to the place where
                 * we put the clusters from the previous block
                 * the logic is ... if we match the clusters from the
                 * current block to the clusters from the previous block
                 * then the clusters from the current block should be added
                 * to the same place as the clusters from the previous block
                 */
                for( frow = 0;
                    (frow < Math.min(fd[i].row.length,fd[i].mns.length)) &&
                    (fd[i].cls[frow][0] != FILLER_VALUE);
                     frow++ ) {
                    bfound = false;
                    for( r = 0; r < i; r++ ) {
                        // if the right block is found, just break
                        if( bfound ) {
                            // right block found ... just break
                            bfound = false;
                            break;
                        }
                        else {
                            // haven't found the right block ... just continue
                        }
                        for( row = 0;
                            (row < Math.min(fd[r].row.length,fd[r].mns.length)) &&
                            (fd[r].cls[row][0] != FILLER_VALUE);
                             row++ ) {
                            // simplified matching of clusters on the cluster mean
                            B    = Math.max(fd[r].B,fd[i].B);
                            dist = dc.ed(fd[r].mns[row],fd[i].mns[frow]);
                            if( dist <= B ) {
                                fd[i].row[frow] = fd[r].row[row];
                                for( col = 0;
                                    (col < clusters[fd[r].row[row]].length) &&
                                    (clusters[fd[r].row[row]][col] != FILLER_VALUE);
                                     col++ ) {
                                    // we will break from here when we have a spot to insert frow
                                }
                                /*
                                 * beginning in the row where the previous block's
                                 * clusters were added, use the found position above
                                 * and add the members of the current block's matching
                                 * clusters
                                 */
                                for( j = 0;
                                    (j < fd[i].cls[frow].length) &&
                                    (fd[i].cls[frow][j] != FILLER_VALUE);
                                     j++ ) {
                                    clusters[fd[r].row[row]][col++] = fd[i].cls[frow][j] + (i * bs);
                                }
                                bfound = true;
                                break;
                            }
                            else {
                                /*
                                 * we didn't find a match for the cluster in the current
                                 * block so check to see if the next row in clusters is empty
                                 * if so, then we have exhausted all available clusters for
                                 * matching, so attempt to add the cluster in the 
                                 * current block as a new cluster in clusters
                                 */
                                if( row + 1 == Math.min(fd[r].row.length,fd[r].mns.length) ) {
                                    col = 0;
                                    // find a row in clusters to insert the current frow
                                    for( trow = 0;
                                        (trow < clusters.length) &&
                                        (clusters[trow][0] != FILLER_VALUE);
                                         trow++ ) {
                                        // we'll break when we find a good row for insertion
                                    }
                                    fd[i].row[frow] = trow;
                                    for( j = 0;
                                        (j < fd[i].cls[frow].length) &&
                                        (fd[i].cls[frow][j] != FILLER_VALUE);
                                         j++ ) {
                                        clusters[trow][col++] = fd[i].cls[frow][j] + (i * bs);
                                    }
                                    bfound = true;
                                    break;
                                }
                                else {
                                    // just continue the search
                                }
                            }
                        }
                    }
                }
            }
        }

        try {
            nm = "mainclusters.out";
            dc.logwriter(nm,clusters,oda);
        }
        catch( IOException ioe ) {
            System.out.println( nm + " - " + ioe.getMessage() );
        }

        return;

    } // end main function (patternmatch)
    
    public static void main( String [] args ) throws FileNotFoundException, IOException {

        int row;
        int col;

        String      ct = null;
        String []   co = {
                          "STRING",
                          "NUMBER",
                          "NUMBER",
                          "NUMBER",
                          "NUMBER",
                          "STRING"
                         };
        String []   co2 = {
                          "STRING",
                          "NUMBER",
                          "NUMBER",
                          "NUMBER",
                          "NUMBER"
                         };
        String [] tokens = null;

        String [][] cl = new String[5][3];
        String [][] da = null;
        String [][] inarr = null;
        String [][] g = null;

        int [] clcol = new int[co2.length];

        FileInputStream fstream;

        DataInputStream in;

        BufferedReader br;

        String strLine;

        HashMap h = new HashMap();

        /*
         * open the data file and read the data into a 2-d array
         */

        // Open the file
        fstream = new FileInputStream(args[0].trim());

        // Get the object of DataInputStream
        in = new DataInputStream(fstream);
        br = new BufferedReader(new InputStreamReader(in));

        // Read File Line By Line
        row = 0;
        while( (strLine = br.readLine()) != null ) {
            tokens = strLine.split( "\\|" );
            if( da == null || da.length < row+1 ) {
                if( da == null )
                    g = new String[row+1][tokens.length];
                else
                    g = new String[row+1][Math.max(da[row-1].length,tokens.length)];
                for( int rows = 0; rows < row; rows++ )
                    System.arraycopy(da[rows],
                                     0,
                                     g[rows],
                                     0,
                                     Math.min(da[rows].length,g[rows].length));
                da = g;
            }
            for( col = 0; col < Math.min(da[row].length,tokens.length); col++ ) {
                da[row][col] = tokens[col].trim();
            }
            row++;
            //System.out.println(row + "\n");
        }

        // need the original (unmodified) data later on
        odata = new String[da.length][da[0].length];
        for( row = 0; row < da.length; row++ ) {
            System.arraycopy(da[row],0,odata[row],0,da[row].length);
        }
        cdata = odata;

        //Close the input stream
        in.close();

        System.out.println("Reading of file completed.....");

        /*
         * define the classes
         * each line in the array will constitute a column,
         * a start value and an end value
         */
        cl[0][0] = "0";
        cl[0][1] = "CNX";
        cl[0][2] = "DLY!DFRL";
        cl[1][0] = "1";
        cl[1][1] = "0";
        cl[1][2] = "2048";
        cl[2][0] = "2";
        cl[2][1] = "0";
        cl[2][2] = "34.13";
        cl[3][0] = "3";
        cl[3][1] = "0";
        cl[3][2] = "7.567";
        cl[4][0] = "4";
        cl[4][1] = "0";
        cl[4][2] = "1";

        adata = new String[3][2];

        adata[0][0] = "CNX";
        adata[0][1] = "0.33";
        adata[1][0] = "DLY";
        adata[1][1] = "0.67";
        adata[2][0] = "DLY!DFRL";
        adata[2][1] = "1.0";

        // specify the columns to classify on
        // for this, everything except dates
        for( int clcolrow = 0; clcolrow < co2.length; clcolrow++ )
            clcol[clcolrow] = Integer.valueOf(cl[clcolrow][0]).intValue();

        inarr = new String[da.length][clcol.length];

        // build the array for classification
        for( row = 0; row < inarr.length; row++ ) {
            for( col = 0; col < inarr[0].length; col++ ) {
                inarr[row][col] = da[row][clcol[col]];
            }
        }

        // create the hashmap entries for testing classify
        h.put("COLUMNS",co2);
        h.put("SUBSETS",cl);
        h.put("DATA",inarr);
        h.put("COUNT",ct);

        // classify the data
        DataClassification dct = new DataClassification(h,false);
        dct.start();
        try {
            dct.join();
        }
        catch( Exception e ) {
            System.out.println( e.getMessage() );
            return null;
        }
        /*
         * instance 0 is started above and MAX_INST is dynamically 
         * computed in its constructor ... so
         * start all other instances in this loop
         */
        DataClassification [] dct1 = new DataClassification[MAX_INST-1];
        for( row = 1; row < MAX_INST; row++ ) {
            dct1[row-1] = new DataClassification(row);
            dct1[row-1].start();
            try {
                dct1[row-1].join();
            }
            catch( Exception e ) {
                System.out.println( e.getMessage() );
            }
        }

        return;

    } // end main function (classify)

    public HashMap driver( String [][] nda ) {

        int row;
        int col;

        String ct = null;

        String [] co     = null;
        String [] co2    = null;
        String [] vecin  = null;
        String [] vecout = null;

        String [][] da    = null;
        String [][] cl    = null;
        String [][] inarr = null;

        int [] clcol = null;

        HashMap h = new HashMap();

        DataClassification dc = new DataClassification();

        DataClassification [] dca = null;

        boolean finishit = false;

        // need the original (unmodified) data later on
        odata = new String[nda.length][nda[0].length];
        for( row = 0; row < nda.length; row++ ) {
            System.arraycopy(nda[row],0,odata[row],0,nda[row].length);
        }

        // need the original (unmodified) data later on
        cdata = odata;

        // set da to nda for later stuff
        da = nda;

        // all columns are treated as strings
        co = new String[da[0].length];
        for( col = 0; col < co.length; col++ ) {
            co[col] = "STRING";
        }

        // all columns are treated as strings
        co2 = new String[co.length];
        for( col = 0; col < co2.length; col++ ) {
            co2[col] = "STRING";
        }

        // classify on all columns
        clcol = new int[co.length];
        for( col = 0; col < clcol.length; col++ ) {
            clcol[col] = col;
        }

        // build the array for classification
        inarr = new String[da.length][clcol.length];
        for( row = 0; row < inarr.length; row++ ) {
            for( col = 0; col < inarr[0].length; col++ ) {
                inarr[row][col] = da[row][clcol[col]];
            }
        }

        /*
         * get the 1st and last value from each column since
         * in pattern matching we have to match on all columns
         * these values are used when dictating the range of
         * values to be used when finding the final range into
         * which the final set should appear
         * for pattern matching we want the full range
         */
        cl    = new String[clcol.length][3];
        vecin = new String[inarr.length];
        for( col = 0; col < cl.length; col++ ) {
            // column number in question
            cl[col][0] = Integer.toString(clcol[col]);
            /*
             * get all of the values of the current
             * column into an array
             */
            for( row = 0; row < vecin.length; row++ ) {
                vecin[row] = inarr[row][col];
            }
            // get the distinct values of the current column
            vecout     = dc.distinct(vecin);
            // beginning value
            cl[col][1] = vecout[0];
            // ending value
            cl[col][2] = vecout[vecout.length - 1];
        }

        // create the hashmap entries for testing classify
        h.put("COLUMNS",co2);
        h.put("SUBSETS",cl);
        h.put("DATA",inarr);
        h.put("COUNT",ct);
        h.put("MRATE","0.50");

        // classify the data
        dc = new DataClassification(h,true);
        dc.start();
        try {
            dc.join();
        }
        catch( Exception e ) {
            System.out.println( e.getMessage() );
            return null;
        }
        /*
         * instance 0 is started above and MAX_INST is dynamically 
         * computed in its constructor ... so
         * start all other instances in this loop
         */
        dca = new DataClassification[MAX_INST-1];
        for( row = 1; row < MAX_INST; row++ ) {
            dca[row-1] = new DataClassification(row);
            dca[row-1].start();
            try {
                dca[row-1].join();
            }
            catch( Exception e ) {
                System.out.println( e.getMessage() );
            }
        }

        // check to see if we can call finish yet
        while( ! finishit ) {
            // begin with finishit == true, unless otherwise directed
            finishit = true;
            // determine the state of all threads
            for( row = 0; row < MAX_INST-1; row++ ) {
                finishit = (finishit && (dca[row].getState() == Thread.State.TERMINATED));
            }
            finishit = (finishit && (dc.getState() == Thread.State.TERMINATED));
            // should we finish ??
            if( finishit ) {
                break;
            }
            else {
                // just continue until all threads have terminated
            }
        }

        // we broke from the loop ... so call finish
        h = dc.finish();

        // add the double data to the return
        h.put("DDATA",data);

        return( h );

    } // end driver function
    
    public String [][] characterize( String [][] in ) {

        int rows = in.length;
        int cols = in[0].length;
        int row;
        int col;
        int curr = 0;
        int max  = 0;
        int len;
        int c;
        int k    = 0;
        int k1;

        boolean repeater = false;

        String [][] out = null;

        /*
         * first we need to count the max number
         * of characters appearing in any of the
         * strings before stripping white space
         * and repeating characters
         */
        for( row = 0; row < rows; row++ ) {
            // count the characters in the current row
            for( col = 0; col < cols; col++ ) {
                // add the length of the current string to curr
                curr += in[row][col].length();
            }
            /*
             * broken from the loop that adds the length
             * of all of the strings in the current row
             * now check to see if the current length is larger
             * than the current max
             */
            if( curr > max ) {
                // set curr max length to curr
                max = curr;
            }
            // set curr to zero for next length computation
            curr = 0;
        }

        // allocate memory for the return
        out = new String[rows][max];

        /*
         * remove whitespace and repeating characters
         * from each row of strings and put each
         * of the characters in individual columns
         */
        for( row = 0; row < rows; row++ ) {
            // set the character iterator at each row of data
            k = 0;
            for( col = 0; col < cols; col++ ) {
                // get the length
                len = in[row][col].length();
                // variable for the out string current character
                if( len > 0 ) {
                    // save the 1st character
                    out[row][k++] = in[row][col].substring(0,1).toLowerCase();
                    for( c = 1; c < len; c++ ) {
                        // skip numbers, special chars and repeating chars
                        if( !in[row][col].substring(c,c+1).matches("[b-dB-Df-hF-Hj-nJ-Np-tP-Tv-xV-XzZ0-9]") ||
                            out[row][k - 1].toLowerCase().charAt(0) ==
                            in[row][col].toLowerCase().charAt(c) ) {
                            continue;
                        }
                        // possibly good character, maybe add it to the return
                        else {
                            /*
                             * want to make it easier to match patterns
                             * by limiting characters for comparison that have
                             * already been included
                             */
                           for( k1 = 0; k1 < k; k1++ ) {
                                repeater = (out[row][k1].toLowerCase().charAt(0) ==
                                            in[row][col].toLowerCase().charAt(c));
                                if( repeater ) {
                                    break;
                                }
                            }
                            if( repeater ) {
                                repeater = false;
                                continue;
                            }
                            else {
                               out[row][k++] = in[row][col].substring(c,c+1).toLowerCase();
                            }
                        }
                    }
                }
            }
            // fill out the remainder of the row with nulls
            for( c = k; c < max; c++ ) {
                // add the null in the current spot
                out[row][c] = "";
            }
        }

        return( out );

    } // end characterize function
    
    public void memory( boolean row, boolean col ) {

        int crows = clusters.length;
        int ccols = clusters[0].length;
        int mrows = means.length;
        int mcols = means[0].length;
        int r;
        int c;
       
        // add a new row
        if( row && col ) {
            // get memory for a new row and col
            ncrows = new int[crows + 1][ccols + 1];
            nmeans = new double[mrows + 1][mcols + 1];
        }
        else {
            // get memory for a new row
            if( row ) {
                ncrows = new int[crows + 1][ccols];
                nmeans = new double[mrows + 1][mcols];
            }
            // get memory for a new col
            else if( col ) {
                ncrows = new int[crows][ccols + 1];
                nmeans = new double[mrows][mcols + 1]; 
            }
            else {
                // do nothing
            }
        }

        for( r = 0; r < ncrows.length; r++ ) {
            // fill the rows with the filler value
            Arrays.fill(ncrows[r],FILLER_VALUE);
            // input the previous values
            if( r < crows ) {
                for( c = 0; c < ncrows[0].length; c++ ) {
                    if( c < ccols ) {
                        ncrows[r][c] = clusters[r][c];
                    }
                    else {
                        // do nothing ... should be filler
                    }
                }
            }
            else {
                // do nothing ... should be filler
            }
        }

        for( r = 0; r < nmeans.length; r++ ) {
            // input the previous values
            if( r < mrows ) {
                for( c = 0; c < nmeans[0].length; c++ ) {
                    if( c < mcols ) {
                        nmeans[r][c] = means[r][c];
                    }
                    else {
                        // do nothing ... should be filler
                    }
                }
            }
            else {
                // do nothing ... should be filler
            }
        }

        // set clusters and means to have the new memory
        clusters = ncrows;
        means    = nmeans;

        return;
    }
    
    public synchronized void classify() throws FileNotFoundException, IOException {

        int row;
        int col;
        int srow;
        int s_rows;
        int prow;
        int instance = this.inst;

        boolean rowbreak     = false;
        boolean colbreak     = false;
        boolean patternmatch = pm;
    
        double currdist = 0.0;

        /* cluster the sampled cases by computing the
         * Euclidean "distances" and judging
         * closeness by an upper bound on
         * the distances
         */
        if( instance == 0 ) {
            clusters[0][0] = srows[0];
        }
        else {
            // do nothing
        }

        for( srow = instance + 1; srow < srows.length; srow += MAX_INST ) {
            rowbreak  = false;
            colbreak  = false;
            if( ! rowbreak ) {
                for( row = 0; row < clusters.length; row++ ) {
                    if( rowbreak ) {
                        break;
                    }
                    colbreak = false;
                    if( ! colbreak ) {
                        for( col = 0; col < clusters[0].length; col++ ) {
                            if( colbreak ) {
                                break;
                            }
                            /* compute the distances of the samples
                             * and determine if they belong in the
                             * same class
                             */
                            if( clusters[row][col] != FILLER_VALUE ) {
                                if( patternmatch ) {
                                    currdist = pmd(row,col,srow);
                                }
                                else {
                                    currdist = ed(row,col,srow);
                                }
                                if( currdist <= B ) {
                                    while( clusters[row][++col] != FILLER_VALUE ) {
                                        continue; // find a place to insert the number
                                    }
                                    clusters[row][col] = srows[srow];
                                    rowbreak           = true;
                                    colbreak           = true;
                                }
                                else {
                                    /* haven't found the cluster where
                                     * this sample should be placed.
                                     * continue the search
                                     */
                                    continue;
                                }
                            }
                            else {
                                if( row != 0 ) {
                                    if( col == 0 ) {
                                        /* haven't found a match and
                                         * the first entry is a -1
                                         * so, start a new class with
                                         * this data
                                         */
                                        clusters[row][col] = srows[srow];
                                        rowbreak           = true;
                                        colbreak           = true;
                                    }
                                    else {
                                        // continue to the next row
                                        colbreak = true;
                                    }
                                }
                                else {
                                    // continue to the next row
                                    colbreak = true;
                                }
                            }
                        }
                    }
                    else {
                        // continue to the next row
                        break;
                    }
                }
            }
            else {
                // continue to the next srow
                break;
            }
        }

        /* compute the mean of
         * the data cases in the current clusters
         */
        for( s_rows = instance;
            (s_rows < means.length) &&
            (clusters[s_rows][0] != FILLER_VALUE);
             s_rows += MAX_INST ) {
            meanvar(s_rows);
        }
      
        /* cluster the remaining cases in the population by comparing the case
         * with the mean of each class
         */
        for( prow = instance; prow < prows.length; prow += MAX_INST ) {
            for( srow = 0;
                (srow < means.length) && (clusters[srow][0] != FILLER_VALUE);
                 srow++ ) {
                if( patternmatch ) {
                    currdist = pmd(srow,prow);
                }
                else {
                    currdist = mtest(srow,prow);
                }
                if( currdist <= B ) {
                    for( col = 0;
                        (col < clusters[srow].length) &&
                        (clusters[srow][col] != FILLER_VALUE);
                         col++ ) {
                        // find a place to insert the number
                    }
                    clusters[srow][col] = prows[prow];
                    /* re-compute the mean of
                     * the data cases in the current cluster
                     * after the new addition
                     */
                    meanvar(srow);
                    break;
                }
                else {
                    /*
                     * check the next row to see if there's
                     * something there other than FILLER_VALUE
                     * in the first column ... if so, then just
                     * continue ... otherwise, just add the
                     * current prow value there
                     */
                    if( (srow + 1 < means.length) &&
                        (clusters[srow+1][0] == FILLER_VALUE) ) {
                        // insert the new value into the first column of row srow+1
                        clusters[srow+1][0] = prows[prow];
                        /* re-compute the mean of
                         * the data cases in the current cluster
                         * after the new addition
                         */
                        meanvar(srow+1);
                        break;
                    }
                    else {
                        // do nothing ... just check the row srow+1
                    }
                }
            }
        }

        return;

    } // end classify function
    
    public HashMap finish() {

        int row;
        int rows;
        int col;
        int srow;
        int len;

        String         nm = null;
        String []    dist = null;
        String []       c = null;
        String []       g = null;
        String [][]    cl = null;
        String [][][]  gh = null;
        String [][][] rcl = null;
                
        HashMap args = hash;
        HashMap h    = new HashMap();

        /*
         * get the number of classes, if defined
         * get the columns to be classified
         * get the classes to be defined
         * get the data
         * all of it from the hashmap passed by the gui
         */
        cl = (String[][])args.get("SUBSETS");

        /*
         * get all of the column numbers
         * to get a unique list
         */
        len = cl.length;
        c   = new String[len];
        for( row = 0; row < len; row++ ) {
            c[row] = cl[row][0].trim();
        }

        // get a unique list of the columns in the class definitions
        dist = distinct(c);

        /*
         * the number of actual classes may be different from what's
         * requested at the onset due to the occurrence of isolated points
         * (outliers) in the original dataset ... also, the defined classes
         * passed in the hashmap on the columns may result in an empty
         * intersection, in which case the data will not be partitioned into
         * the classes that were defined by the user ... so, N may not hold
         * the actual number of classes in the clusters array ... we need to
         * count the clusters ... the end of the count will be signified by
         * the presence of -1 in the first column of a row in the array ...
         * this is a good demarcation since clusters contains array indices of
         * rows in the original dataset and these will always be non-negative
         */
        for( rows = 0;
            (rows < clusters.length) &&
            (clusters[rows][0] != FILLER_VALUE);
             rows++ ) {
            // upon break, we will have a count of the clusters in clusters
        }
       
        /*
         * at this point, we need to have clusters with the original data indices
         * if we didn't classify the entirety of the data
         */
        if( poprows != null ) {
            for( row = 0; row < rows && clusters[row][0] != FILLER_VALUE; row++ ) {
                for( col = 0;
                    (col < clusters[0].length) &&
                    (clusters[row][col] != FILLER_VALUE);
                     col++ ) {
                    clusters[row][col] = poprows[clusters[row][col]];
                }
            }
        }
        else {
            // just go on ... we classified everything and clusters is good to go
        }

        /*
         * get memory for the return of the class definitions
         * one block for each counted class and one row for each
         * column in the original dataset so that we can return column num,
         * the min and max of all the data members in each column and each class
         */
        rcl = new String[rows][dist.length][3];

        /*
         * populate the return classes (rcl) per the comments above
         * this variable will hold the values from the columns of the
         * original data set defined by the limiting clusters
         */
        gh = new String[rows][dist.length][ROWS];

        /*
         * row represents the current cluster in clusters
         */
        for( row = 0; row < rows; row++ ) {
            /*
             * col represents the current column in the cluster
             * upon which we want to get the min and max
             */
            for( col = 0; col < dist.length; col++ ) {
                /*
                 * srow will represent the index of the current element
                 * in the current cluster
                 */
                for( srow = 0;
                    (srow < ROWS) &&
                    (clusters[row][srow] != FILLER_VALUE);
                     srow++ ) {
                    /*
                     * getting the associated data value from
                     * the original data set
                     */
                    gh[row][col][srow] = cdata[clusters[row][srow]][Integer.valueOf(dist[col]).intValue()];
                }
                /*
                 * we have broken from the loop filling the array gh[row][col]
                 * copy gh[row][col] and get just the right size
                 */
                g = new String[srow];
                System.arraycopy(gh[row][col],0,g,0,srow);
                Arrays.sort(g);
                // populate the return class for the current cluster/column
                rcl[row][col][0] = dist[col];      // column number
                rcl[row][col][1] = g[0];           // min
                rcl[row][col][2] = g[g.length-1];  // max
            }
        }

        // perform a garbage collection before returning
        System.gc();

        // create the hashmap entries for testing classify
        h.put("CLASSES",rcl);
        h.put("CLUSTERS",clusters);
        h.put("MEANS",means);

        return( h );

    } // end finish function
    
    public void sampleset( int [] s, int pop, int beg ) {

        int srow;
        int k;
        int amax;
        int len = s.length;

        double r;
        double F;
        double pel;
        double plk;
        double ffk;

        /*
         * use a constant seed for the random number generator
         * so that the classes are built the same way every time
         * otherwise, if a different seed is used everytime, then
         * the samples will change and the computed mean will be
         * different after each addition ... as such, following
         * additions will have distances computed differently and
         * may end up in different classes as a result ... this is
         * expected, however ... you cannot determine ordering of
         * additional data points since we select class representatives
         * at random ... we just want the same random set every time ...
         * if it is desired to have a different seed everytime, then use
         * Date d = new Date();
         * Random rand = new Random( d.getTime() );
         */
        Random rand = new Random(0);

        /* generate M_SQR random numbers in the
         * interval from 0 to 1
         */
        for( srow = 0; srow < len; srow++ ) {
            r = ((double)rand.nextInt()/(double)Integer.MAX_VALUE);
            F = 0.0;
            /* when we go over the probability "r"
             * then we are done with the search
             */
            k = 0;
            while( F <= r ) {
                /* utilizing the inverse of the Poisson cumulative distribution
                 * func. to find the values k that map to the range values
                 * of the distribution function generated by the
                 * random number generator
                 */
                pel = Math.pow( e, -L );
                plk = Math.pow( L, k );
                ffk = fact((double)k);
                F += pel * (plk / ffk);
                k++;
            }
            if( srow == 0 ) {
                s[srow] = k + 1 + beg;
            }
            else {
                s[srow] = k + 1 + s[srow - 1];
            }
        }
   
        /* need to scale the row numbers since
         * the values now in s can go beyond
         * the total number of rows in the population
         */
        amax = arraymax(s);
        for( srow = 0; srow < len; srow++ ) {
            s[srow] = (int)(((double)s[srow]/(double)(amax + 100)) * (double)pop);
        }

        return;

    } // end sampleset function
    
    public void samples( String [][] cl ) {

        int srow;
        int prow;
        int row;
        int k;
        int curr;
        int prev;
        int len;
        int pop;

        /*
         * the idea is to get the initial set of samples from the defined
         * clusters ... then get the rest of the M_SQR samples and merge
         * the 2 sets of samples together
         */
        int [] sr1 = samplepart(cl);
        int [] sr2 = null;

        // size of the population (which may have been modified by defined clusters
        pop   = data.length;

        // fill srows with samples

        /*
         * it's possible that sr1 has used up the entirety of the samples
         * that we want to take ... in this event, we don't need sr2 as it
         * would be null in any event ... so, if sr1.length == S_ROWS then
         * skip taking additional samples
         */
        if( sr1 != null ) {
            /*
             * the distribution function is not necessarily a 1-to-1 mapping ...
             * thus, we may have found the same k values (belonging to different
             * events) that map to possibly different probabilities as a result, 
             * which are generated by the random number generator ...
             * so, we'll make the list of sample rows to contain unique values
             */
            sr1 = distinct(sr1);
            if( sr1.length < S_ROWS ) {
                // need additional samples
                sr2 = new int[S_ROWS-sr1.length];
                sampleset(sr2,pop,arraymax(sr1));
                /*
                 * the distribution function is not necessarily a 1-to-1 mapping ...
                 * thus, we may have found the same k values (belonging to different
                 * events) that map to possibly different probabilities as a result, 
                 * which are generated by the random number generator ...
                 * so, we'll make the list of sample rows to contain unique values
                 */
                sr2    = distinct(sr2);
                S_ROWS = sr1.length + sr2.length;
            }
            else {
                S_ROWS = sr1.length;
            }
        }
        else {
            /*
             * all samples will be found at this point
             * there is no sr1 so the count from that sample set is 0
             */
            sr2 = new int[S_ROWS];
            sampleset(sr2,pop,0);
            /*
             * the distribution function is not necessarily a 1-to-1 mapping ...
             * thus, we may have found the same k values (belonging to different
             * events) that map to possibly different probabilities as a result, 
             * which are generated by the random number generator ...
             * so, we'll make the list of sample rows to contain unique values
             */
            sr2    = distinct(sr2);
            S_ROWS = sr2.length;
        }

        /*
         * redefinition of srows and prows since it may be necessary
         */
        srows  = new int[S_ROWS];
        P_ROWS = ROWS - S_ROWS;

        // merge the 2 sets of samples together
        if( sr1 != null ) {
            for( srow = 0; srow < sr1.length; srow++ ) {
                srows[srow] = sr1[srow];
            }
            if( sr2 != null ) {
                for( srow = 0; srow < sr2.length; srow++ ) {
                    srows[sr1.length+srow] = sr2[srow];
                }
            }
            else {
                // no additional samples since sr2 is null
            }
        }
        else {
            // sr2 will contain all of the samples
            for( srow = 0; srow < sr2.length; srow++ ) {
                srows[srow] = sr2[srow];
            }
        }

        /*
         * since we merge srows from 2 randomly generated arrays
         * it's possible to have the ordering or rows a bit chaotic
         * this is not desirable ... so sort the array before use
         */
        srows  = distinct(srows);
        S_ROWS = srows.length;

        Arrays.sort(srows);

        /*
         * as a result of the dataset being (possibly) modified, prows (which
         * contains the remainder of the samples) should be sized as well
         */
        len    = srows.length;
        P_ROWS = pop - len;
        prows  = new int[P_ROWS];

        // populate prows with the rest of the population
        k = 0;
        prev = 0;
        /* the loop terminator "<=" is required
         * in order to capture the last cases
         * from the population
         */
        for( srow = 0; srow <= len; srow++ ) {
            curr = prev >= srows[len-1] + 1 ? pop : (srow < len ? srows[srow] : pop);
            for( prow = prev; prow < curr; prow++ ) {
                prows[k++] = prow;
            }
            // prev should be the next value NOT in srows
            row = 0;
            while( true ) {
                prev = curr + row;
                if( prev < pop ) {
                    if( srow + row < srows.length && prev == srows[srow+row] ) {
                        /*
                         * add 1 to row since this is a successive number sampled
                         * and cannot be used as the lower bound when getting the
                         * rest of the population rows
                         */
                        row++;
                    }
                    else {
                        /*
                         * found a good number ... adding the previous row number
                         * to srow since the increment will happen again above
                         */
                        srow += (row - 1);
                        break;
                    }
                }
                else {
                    // nothing more to do ... just break and end
                    break;
                }
            }
        }

        return;

    } // end samples function
    
    public int[] samplepart( String [][] cl ) {

        int cls;
        int clss;
        int blk;
        int row;
        int col;
        int arow = 0;
        int acol;
        int rows = data.length;
        int cols = data[0].length;
        int len  = cl.length;

        int [] s = null;

        double low;
        double high;

        double [][][] dat = null;

        String curr = null;

        String [] c    = new String[len];
        String [] dist = null;

        /*
         * get all of the column numbers
         * to get a unique list
         */
        for( row = 0; row < len; row++ ) {
            c[row] = cl[row][0].trim();
        }

        // get a unique list
        dist = distinct(c);

        /*
         * going to populate a 2-d array with the
         * successive intersections of each of the
         * classes that have been defined on the columns
         */
        clss = dist.length + 1;
        dat  = new double[clss][rows][cols+1];
        /*
         * going to start with the original data
         * set ... so, let's copy it to the dat
         * array ... initialize all the others
         * with -1.0
         */
        for( cls = 0;
            (cls < clss) && (cls < dat.length);
             cls++ ) {
            for( row = 0;
                (row < rows) && (row < Math.min(data.length,dat[cls].length));
                 row++ ) {
                if( cls == 0 ) {
                    // the original data set
                    for( col = 0; col < Math.min(data[row].length,dat[cls][row].length); col++ ) {
                        dat[cls][row][col] = data[row][col];
                    }
                    /*
                     * need to keep track of the row indices
                     * for later when we take the samples
                     */
                    dat[cls][row][cols] = row;
                }
                else {
                    /*
                     * each successive data set will be a subset
                     * of the previous and will depend on the
                     * restrictions given by the user-defined clusters
                     */
                    Arrays.fill(dat[cls][row],(double)FILLER_VALUE);
                }
            }
        }

        /*
         * for each unique column defining the classes
         * create a new block of data that's more restricted
         * than the last one
         * cls is started at 1 since index 0 corresponds to the
         * original data set
         */
        for( cls = 1; cls < clss; cls++ ) {
            // current column defining a class
            curr = dist[cls-1].trim();
            col  = Integer.valueOf(curr).intValue();
            arow = 0;
            for( blk = 0; blk < len; blk++ ) {
                if( curr.compareTo(cl[blk][0].trim()) == 0 ) {
                    low  = Double.valueOf(cl[blk][1].trim()).doubleValue();
                    high = Double.valueOf(cl[blk][2].trim()).doubleValue();
                    for( row = 0; row < rows; row++ ) {
                        /*
                         * the low and high could actually be reversed in
                         * cases where strings have been converted to a
                         * numeric representation
                         */
                        if( dat[cls-1][row][col] >= Math.min(low,high) &&
                            dat[cls-1][row][col] <= Math.max(low,high) ) {
                            // fits the criteria, so add it to the next dat
                            for( acol = 0; acol < cols+1; acol++ ) {
                                dat[cls][arow][acol] = dat[cls-1][row][acol];
                            }
                            // increment arow for the next row to be added
                            arow++;
                        }
                        else {
                            // not a row to add ... just continue
                            continue;
                        }
                    }
                }
                else {
                    // not the right column ... just continue
                    continue;
                }
            }
            /*
             * once break from the loop, we have the number of rows in
             * the previous data set ... namely arow
             * we should use this as the loop terminator
             * however, initially, this value is the same as the length
             * of the original data set
             */
            rows = arow;
        }

        /*
         * now that the data has been selected according
         * to the defined clusters ... let's get the samples
         * first we need to get memory for s while noting
         * that the number of samples that we need is given
         * by the proportion of (arow / data.length) * M_SQR
         */
        rows  = (int)Math.ceil(((double)arow/(double)data.length) * M_SQR);
        /*
         * if rows == 0 then we'll set the array length to 1
         * just to get 1 row in this sample if arow > 0
         */
        if( arow > 0 ) {
            /*
             * since arow is positive, then there are rows that match the search
             * based upon the user's defined classes ... hence, we will modify
             * what's currently stored in data since we only want to classify
             * what's contained in the match ... first, we will redeclare data
             */
            for( row = 0; row < data.length; row++ ) {
                System.arraycopy(dat[cls-1][row],0,data[row],0,COLS);
            }
            s = new int[rows > 0 ? rows : 1];
            // get at least 1 sample from the population of arow rows
            sampleset(s,arow,0);
            /*
             * for each row in s, we need to substitute the true
             * array index for the original data set, which was included
             * in the last column of each dat array
             */
            poprows = new int[arow];
            for( row = 0; row < poprows.length; row++ ) {
                poprows[row] = (int)dat[cls-1][row][cols];
            }
        }
        else {
            // just return s as null
        }

        return(s);

    } // end samplepart function

    public double fact( double k ) {

        return( k <= 0.0 ? 1.0 : k * fact(k - 1.0) );

    } // end factorial function
    
    public int rowmax( int [][] clus ) {

        int row;
        int rows = 0;

        for( row = 0;
            (row < clus.length) &&
            (clus[row][0] != FILLER_VALUE);
             row++ ) {
            rows++;
        }

        return( rows );

    } // end rowmax function
    
    public int colmax( int [][] clus ) {

        int row;
        int col;
        int cols = 0;
        int max  = 0;

        for( row = 0;
            (row < clus.length) &&
            (clus[row][0] != FILLER_VALUE);
             row++ ) {
            for( col = 0;
                (col < clus[row].length) &&
                (clus[row][col] != FILLER_VALUE);
                 col++ ) {
                cols++;
            }
            if( cols > max ) {
                max = cols;
            }
            else {
                // keep the current max
            }
            cols = 0;
        }

        return( max );

    } // end colmax function

    public int arraymax( int [] s ) {

        int curr = s[0];
        int row;

        for( row = 0; row < s.length; row++ ) {
            if( s[row] >= curr ) { 
                curr = s[row];
            }
            else {
                // just keep the curr value
            }
        }

        return(curr);

    } // end arraymax function

    public int arraymin( int [] s ) {

        int row;
        int len = s.length;

        int [] sr = new int[len];

        for( row = 0; row < len; row++ ) {
            sr[row] = -s[row];
        }

        return(-arraymax(sr));

    } // end arraymin function

    public double arraymax( double [] s ) {

        double curr = s[0];
        int row;

        for( row = 0; row < s.length; row++ ) {
            if( s[row] >= curr ) { 
                curr = s[row];
            }
            else {
                // just keep the curr value
            }
        }

        return(curr);

    } // end arraymax function

    public double arraymin( double [] s ) {

        int row;
        int len = s.length;

        double [] sr = new double[len];

        for( row = 0; row < len; row++ ) {
            sr[row] = -s[row];
        }

        return(-arraymax(sr));

    } // end arraymin function

    public double ed( int row, int col, int srow ) {

        int lcol;

        double [] x = data[clusters[row][col]];
        double [] y = data[srows[srow]];

        double s = 0.0;

        // compute the dividend for the normal euclidean distance
        for( lcol = 0; lcol < COLS; lcol++ ) {
            s += (Math.pow( x[lcol] - y[lcol], 2.0 ));
        }

        return( Math.sqrt(s) );

    } // end ed function

    public double ed( double [] x, double [] y ) {

        int lcol;
        int tmin = Math.min(x.length,y.length);

        double s = 0.0;

        // compute the dividend for the normal euclidean distance
        for( lcol = 0; lcol < tmin; lcol++ ) {
            s += (Math.pow( x[lcol] - y[lcol], 2.0 ));
        }

        return( Math.sqrt(s) );

    } // end ed function

    public double d( double [] x, double [] y ) {

        /* modify the euclidean distance so that
         * all distances are less than or equal to one
         */
        return( ed(x,y)/Math.sqrt(COLS) );

    } // end d function

    public double pmed( double [] x, double [] y ) {

        String empty = "";
        String vnull = replace(empty,adata);

        // get the value assigned to the null string
        double val = vnull != null ? Double.valueOf(vnull).doubleValue() : (double)FILLER_VALUE;
        double ilen = adata.length != 0 && adata[0].length != 0   ?
                      Double.valueOf(adata[1][1]).doubleValue() -
                      Double.valueOf(adata[0][1]).doubleValue() :
                      0;
        double len  = 0.5 * ilen;

        double [] x1 = new double[x.length];
        double [] y1 = new double[y.length];

        int col;

        // replace the null values so it won't affect the distance calc.
        for( col = 0; col < x.length; col++ ) {
            if( val - len < x[col] && x[col] < val + len ) {
                x1[col] = 0.0;
            }
            else {
                x1[col] = x[col];
            }
        }
        for( col = 0; col < y.length; col++ ) {
            if( val - len < y[col] && y[col] < val + len ) {
                y1[col] = 0.0;
            }
            else {
                y1[col] = y[col];
            }
        }

        /* 
         * modify the euclidean distance so that
         * all distances are less than or equal to one
         */
        return( ed(x1,y1) );

    } // end pmed function

    public double pmd( int srow, int prow ) {

        double [] x = means[srow];
        double [] y = data[prows[prow]];

        return( pmd(x,y) );

    } // end pmd function

    public double pmd( int row, int col, int srow ) {

        double [] x = data[clusters[row][col]];
        double [] y = data[srows[srow]];

        return( pmd(x,y) );

    } // end pmd function
    
    public double pmd( double [] x, double [] y ) {

        double len;
        double num;
        double val;
        double dist;
        double ilen = adata.length != 0 && adata[0].length != 0   ?
                      Double.valueOf(adata[1][1]).doubleValue() -
                      Double.valueOf(adata[0][1]).doubleValue() :
                      0;
        double rate = RATE;
        double merr = 1.0 - MRATE;

        int xcol;
        int ycol;
        int zcol;
        int lcol  = 0;
        int cnt   = 0;
        int bad   = 0;
        int xnull = 0;
        int ynull = 0;
        int zln   = 0;
        int lgd   = 0;

        int [] z = new int[x.length];

        boolean found  = false;
        boolean breakx = false;

        String empty = "";
        String vnull = replace(empty,adata);

        // initialize the z array with -1 in all slots
        for( zcol = 0; zcol < z.length; zcol++ ) {
            z[zcol] = FILLER_VALUE;
        }

        // get the value assigned to the null string
        val = vnull != null                       ?
              Double.valueOf(vnull).doubleValue() :
             (double)FILLER_VALUE;

        /*
         * half way bewteen the current col and next
         * this will be the assumed standard deviation
         */
        len = 0.5 * ilen;

        // count the number of nulls in x for later use
        for( xcol = 0; xcol < x.length; xcol++ ) {
            // continue if x[xcol] is null ... no need to match
            if( val - len < x[xcol] && x[xcol] < val + len ) {
                xnull++;
            }
        }
            
        // now check to see if this is a match
        for( ycol = 0; ycol < y.length; ycol++ ) {
            // continue if y[ycol] is null ... no need to match
            if( val - len < y[ycol] && y[ycol] < val + len ) {
                ynull++;
            }
            /*
             * for each coordinate of the new value, test it against
             * all coordinates of the previous value
             * if a match is found, count it
             */
            for( xcol = 0; xcol < x.length; xcol++ ) {
                // found what we were looking for ... go to the next y value
                if( breakx ) {
                    breakx = false;
                    break;
                }
                // break if x[xcol] is null ... no need to continue
                if( val - len < x[xcol] && x[xcol] < val + len ) {
                    break;
                }
                // if current y col "close" to x col, then count it
                if( x[xcol] - len < y[ycol] && y[ycol] < x[xcol] + len ) {
                    // see if this column has been found before
                    for( zcol = 0; zcol < z.length; zcol++ ) {
                        found = (z[zcol] == xcol);
                        if( found ) {
                            break;
                        }
                        else {
                            // not found ... add it
                            z[lcol++] = xcol;
                            breakx = true;
                            break;
                        }
                    }
                }
                else {
                    // not a match ... just continue
                    continue;
                }
            }
        }

        /*
         * count the number of characters in the right sequence
         * if more than half are out of sequence then the
         * string will be rejected as a match
         */
        for( zcol = 1; zcol < lcol; zcol++ ) {
            // characters not reversed
            if( z[lgd] < z[zcol] ) {
                // matching characters found to be in the right order
                if( z[lgd] + 1 == z[zcol] ) {
                    cnt++;
                }
                else {
                    // one character skipped, count as good and bad
                    if( z[lgd] + 1 == z[zcol] - 1 ) {
                        cnt++;
                        //bad++;
                    }
                    // multiple skipped
                    else {
                        bad++;
                    }
                }
            }
            // characters reversed;
            else {
                // matching characters found to be in the right order
                if( z[zcol] + 1 == z[lgd] ) {
                    cnt++;
                    //bad++;
                }
                else {
                    // one or more skipped
                    bad++;
                }
            }
            // set last good character found
            lgd = zcol;
        }

        // length of the comparator string without trailing nulls
        zln = z.length - Math.min(xnull,ynull);

        // include in "bad" the number of characters not found
        bad += (zln - lcol);

        // percentage of characters not in the correct sequence
        num = Math.max(((double)zln-(double)cnt)/(double)zln,(double)bad/(double)zln);

        /*
         * compute the mean error rate in successfully matched patterns
         * where a successfully matched pattern is one in which at least
         * half of all characters are a match and are in the correct order
         */
        if( num <= merr ) {
            // number of errors this time out
            errvar[COUNT] = (bad + zln - cnt);
            // total errors in positively matching patterns
            ERRORS += errvar[COUNT];
            /*
             * we want to measure the error rate in matches since
             * we reject matches based upon exceeding the error
             * rate of patterns not matching
             */
            COUNT++;
            rate = (double)ERRORS/(double)COUNT;
            // compute the variance
            variance = 0.0;
            if( COUNT > 1 ) {
                for( zcol = 0; zcol < COUNT; zcol++ ) {
                    variance += Math.pow((errvar[zcol]-rate),2.0);
                }
                variance /= (COUNT - 1);
            }
            else {
                // variance is zero when there is only one sample
            }
            // the rate of error that includes three standard deviations
            RATE = rate + (3.0 * Math.sqrt(variance));
            dist = num * (1.0/rate) * B;
            /*
             * if dist <= B then we can just return it
             * otherwise, we may as well look at the
             * euclidean distance just to be sure
             * that this is not a match for the current class
             */
            if( dist > B ) {
                dist = pmed(x,y);
                /*
                 * if dist <= B then attempt to
                 * realign the word so that the
                 * class mean computations are
                 * the best for later comparisons
                 */
                if( dist <= B ) {
                    /*
                     * these are just numbers
                     * so, when we have a match, we
                     * can just copy one set of numeric
                     * representations to the other
                     */
                    System.arraycopy(x,0,y,0,Math.min(x.length,y.length));
                }
                else {
                    // no need to copy, not a match
                }
            }
            else {
                /*
                 * these are just numbers
                 * so, when we have a match, we
                 * can just copy one set of numeric
                 * representations to the other
                 */
                System.arraycopy(x,0,y,0,Math.min(x.length,y.length));
            }
            return( dist );
        }
        else {
            /*
             * more than half of the characters don't match
             * so in a last ditch effort to match x and y,
             * return the euclidean distance between x and y
             */
            return( pmed(x,y) );
        }

    } // end pmd function

    public double mean( double [] in ) {

        int col;

        double out = 0.0;

        for( col = 0; col < in.length; col++ ) {
            if( in[col] == 0.0 ) {
                break;
            }
            else {
                out += in[col];
            }
        }

        /* for an unbiased estimate of the true
         * mean, the divisor should be equal to
         * the total number of non-zero samples.
         * since the array index is always
         * equal to the sample size upon break,
         * then just use the current array index
         */
        if( col > 0 ) {
            out /= (double)col;
        }
        else {
            out = 0.0;
        }

        return(out);

    } // end mean function

    public double smean( double [] in, int cutoff ) {

        double [] out = new double[cutoff];

        int col;

        for( col = 0;
            (col < cutoff) && (col < Math.min(in.length,out.length));
             col++ ) {
            out[col] = in[col];
        }

        return(mean(out));

    } // end smean function

    public void meanvar( int s_rows ) {

        int col;
        int dcol;

        int [] crow = clusters[s_rows];

        double [] clus = new double[crow.length];

        /* get all of the cases that form the
         * cluster and place them into an array
         */
        //for( col = 0; col < Math.min(data[0].length,means[s_rows].length); col++ ) {
        for( col = 0; col < data[0].length; col++ ) {
            for( dcol = 0;
                (dcol < crow.length) && (crow[dcol] != FILLER_VALUE);
                 dcol++ ) {
                clus[dcol] = data[crow[dcol]][col];
            }
            /* get the mean for each
             * column(row) of the cluster of cases
             */
            means[s_rows][col] = mean(clus);
        }

        return;

    } // end meanvar function

    public double mag( double [] v ) {

        double [] o = new double[v.length];

        return( ed(v,o) );

    } // end mag function

    public double mtest( int srow, int prow ) {

        double [] mout = means[srow];
        double [] d    = data[prows[prow]];

        int col;
        int len = Math.min(mout.length,d.length);

        double [] dff  = new double[len];

        for( col = 0; col < len; col++ ) {
            dff[col] = mout[col] - d[col];
        }

        return( mag(dff) );

    } // end mtest function
    
    public void logwriter( String filename, double [][] data ) throws IOException {

        String f = filename + "." + Integer.toString(inst);

        File file = new File(f);

        FileWriter fstream = new FileWriter(f);

        BufferedWriter out = new BufferedWriter(fstream);

        int row;
        int col;

        file.createNewFile();

        /*
         * write all data from the 2-d array of
         * doubles to a file
         */
        for( row = 0; row < data.length; row++ ) {
            for( col = 0; col < data[0].length; col++ ) {
                if( col == data[0].length - 1 ) {
                    out.write( Double.toString( data[row][col] ) + "\n" );
                }
                else {
                    out.write( Double.toString( data[row][col] ) + "|" );
                }
            }
        }

        out.close();

        return;

    } // end logwriter function
    
    public void logwriter( String filename, int [] data ) throws IOException {

        String f = filename + "." + Integer.toString(inst);

        File file = new File(f);

        FileWriter fstream = new FileWriter(f);

        BufferedWriter out = new BufferedWriter(fstream);

        int row;

        file.createNewFile();

        /*
         * write all data from a 1-d array of
         * ints to a file
         */
        for( row = 0; row < data.length; row++ ) {
            if( row == data.length - 1 ) {
                out.write( Integer.toString( data[row] ) );
            }
            else {
                out.write( Integer.toString( data[row] ) + "\n" );
            }
        }

        out.close();

        return;

    } // end logwriter function
    
    public void logwriter( String filename, int [][] data ) throws IOException {

        String f = filename + "." + Integer.toString(inst);

        File file = new File(f);

        FileWriter fstream = new FileWriter(f);

        BufferedWriter out = new BufferedWriter(fstream);

        int row;
        int col;

        file.createNewFile();

        /*
         * write all data from a 2-d array of
         * ints to a file
         */
        for( row = 0; row < data.length; row++ ) {
            for( col = 0; col < data[0].length; col++ ) {
                if( col == data[0].length - 1 ) {
                    out.write( Integer.toString( data[row][col] ) + "\n" );
                }
                else {
                    out.write( Integer.toString( data[row][col] ) + "|" );
                }
            }
        }

        out.close();

        return;

    } // end logwriter function
    
    public void logwriter( String filename, int [][] data, String [][] oda ) throws IOException {

        String f = filename + "." + Integer.toString(inst);

        File file = new File(f);

        FileWriter fstream = new FileWriter(f);

        BufferedWriter out = new BufferedWriter(fstream);

        int row;
        int col;
        int cls;
        int dcol;

        file.createNewFile();

        /*
         * write all data from a 2-d array of
         * ints to a file
         */
        for( row = 0; row < data.length; row++ ) {
            cls = row + 1;
            if( data[row][0] == FILLER_VALUE ) {
                continue;
            }
            else {
                out.write( "\n********** CLASS " + cls + " **********\n" );
            }
            for( col = 0; col < data[0].length; col++ ) {
                if( data[row][col] == FILLER_VALUE ) {
                    break;
                }
                else {
                    for( dcol = 0; dcol < oda[0].length; dcol++ ) {
                        if( dcol == oda[0].length - 1 ) {
                            out.write( oda[data[row][col]][dcol] + "\n" );
                        }
                        else {
                            out.write( oda[data[row][col]][dcol] + "|" );
                        }
                    }
                }
            }
        }

        out.close();

        return;

    } // end logwriter function
    
    public void condition( String [] co, String [][] cl, String [][] da ) {

        int col;        
        int row;
        int rows = da.length;
        int cols = co.length;

        double dmax = 0.0;

        double [] d = new double[rows];

        String [][] av = null;

        // get memory for data to be the same size as da
        data = new double[rows][cols];

        /*
         * for each string in the list of column
         * data types, convert all strings into
         * a number
         */
        for( col = 0; col < cols; col++ ) {
            /*
             * if it's a string then we got work
             * to do converting the string to values
             * that can be used when computing distances
             */
            if( co[col].compareTo("STRING") == 0 ) {
                /*
                 * assign values between 0 and 1 for
                 * each distinct value in c
                 */
                av = adata;
                /*
                 * modify the class definitions
                 * with the assigned values
                 */
                modify(Integer.toString(col),av,cl);
                /*
                 * modify the data columns
                 * with the assigned values
                 */
                modify(col,av,da);
            }
            else {
                /*
                 * this is just a column of numbers
                 * we can use these as is
                 */
                for( row = 0; row < rows; row++ ) {
                    data[row][col] = Double.valueOf(da[row][col].trim()).doubleValue();
                    // capturing the column of values for later use
                    d[row] = data[row][col];
                }
                /*
                 * now we need to take the column of data and divide each value
                 * in the column by the maximum of that column in order to produce
                 * data that is between 0.0 and 1.0 ... Note that arraymax could
                 * return a negative number
                 */
                dmax = Math.abs(arraymax(d));
                for( row = 0; row < rows; row++ ) {
                    // get the values between 0.0 and 1.0
                    data[row][col] /= (dmax > 0.0 ? dmax : 1.0);
                    // now convert it back to a string for later
                    da[row][col] = String.valueOf(data[row][col]).toString();
                }
                /*
                 * now for the cluster definitions, we just need to divide the max
                 * and min by the max of the data for scaling
                 */
                for( row = 0; row < cl.length; row++ ) {
                    if( Integer.valueOf(cl[row][0]).intValue() == col ) {
                        // get the values between 0.0 and 1.0
                        cl[row][1] = String.valueOf(Double.valueOf(cl[row][1]).doubleValue()/dmax).toString();
                        // get the values between 0.0 and 1.0
                        cl[row][2] = String.valueOf(Double.valueOf(cl[row][2]).doubleValue()/dmax).toString();
                    }
                    else {
                        // not the right column ... just continue
                        continue;
                    }
                }
            }
        }

        return;

    } // end condition function
    
    public String[] distinct( String [] c ) {

        HashSet<String> dist = new HashSet<String>();

        int row;
        int rows;

        String [] s = null;

        Iterator<String> is;

        for( row = 0; row < c.length; row++ ) {
            /*
             * the add method will only add new
             * values to the hash set if it does
             * not already exist ... unique only
             * which is what's desired for the return
             */
            dist.add(c[row]);
        }

        rows = dist.size();

        /*
         * going to iterate over the elements
         * in the hash set one by one
         */
        is = dist.iterator();

        s = new String[rows];

        row = 0;
        while( is.hasNext() ) {
            s[row] = is.next();
            row++;
        }

        Arrays.sort(s);

        return(s);

    } // end distinct (String[]) function
    
    public String[] distinct( String [][] c ) {

        int row;
        int rows = c.length;
        int slen;
        int olen;
        int hlen;

        String [] s    = null;        
        String [] out  = null;
        String [] hold = null;

        for( row = 0; row < rows; row++ ) {
            // get the distinct characters from this row
            s    = distinct( c[row] );
            slen = s.length;
            if( row == 0 ) {
                // first time through, allocate initial memory to out
                out = new String[slen];
                // copy the current string to out
                System.arraycopy( s, 0, out, 0, slen );
            }
            else {
                // length of out before additions
                olen = out.length;
                // reallocate memory for the new additions
                hold = new String[olen + slen];
                // add old out to hold
                System.arraycopy( out, 0, hold, 0, olen );
                // add new s to hold
                System.arraycopy( s, 0, hold, olen, slen );
                // length of hold after additions
                hlen = hold.length;
                // reallocate out
                out = new String[hlen];
                // copy hold to out
                System.arraycopy( hold, 0, out, 0, hlen );
            }
        }

        /*
         * At each iteration of the loop above, new distinct
         * additions were added to the return array.  But, each
         * iteration may have introduced new copies of characters
         * already added.  So, make out distinct one more time.
         */
        hold = distinct( out );

        return( hold );

    } // end distinct (String[][]) function
    
    public int[] distinct( int [] c ) {

        HashSet<Integer> dist = new HashSet<Integer>();

        int row;
        int rows;

        int [] s = null;

        Iterator<Integer> is;

        for( row = 0; row < c.length; row++ ) {
            /*
             * the add method will only add new
             * values to the hash set if it does
             * not already exist ... unique only
             * which is what's desired for the return
             */
            dist.add(c[row]);
        }

        rows = dist.size();

        /*
         * going to iterate over the elements
         * in the hash set one by one
         */
        is = dist.iterator();

        s = new int[rows];

        row = 0;
        while( is.hasNext() ) {
            s[row] = is.next();
            row++;
        }

        Arrays.sort(s);

        return(s);

    } // end distinct (Integer) function
    
    public String[][] assign( String [] dist ) {

        int len = dist.length;
        int row;

        double segment = len > 0 ? 1.0/(double)len : 0.0;

        String [][] av = new String[len][2];

        /*
         * building a 2-d array of original string
         * values and a unique numeric representation
         * the numeric representation is needed when
         * computing distances
         */
        for( row = 0; row < len; row++ ) {
            av[row][0] = dist[row];
            av[row][1] = Double.valueOf((((2.0 * (double)row) + 1.0) / 2.0) * segment).toString();
        }

        return(av);

    } // end assign( String [] dist ) function
    
    public void modify( String col, String [][] av, String [][] cl ) {

        int row;

        for( row = 0; row < cl.length; row++ ) {
            /*
             * if cl[row][0] is a match to the column
             * that was assigned values, then substitute the
             * character value in cl for a numeric one from av
             */
            if( cl[row][0].compareTo(col) == 0 ) {
                // make the substitution of the start value
                cl[row][1] = replace(cl[row][1],av);
                // make the substitution of the end value
                cl[row][2] = replace(cl[row][2],av);
            }
            else {
                // leave these values as they are
                continue;
            }
        }

        return;

    } // end modify (class definitions) function
    
    public void modify( int col, String [][] av, String [][] da ) {

        int row;
        int irow;

        for( row = 0; row < da.length; row++ ) {
            /*
             * for every row in the "col" column
             * check for a matching value in av
             * and convert the value to a unique
             * double value for use when computing
             * distances
             */
            for( irow = 0; irow < av.length; irow++ ) {
                if( da[row][col].compareTo(av[irow][0]) == 0 ) {
                    // found the right match ... convert to a double
                    da[row][col] = av[irow][1];
                }
                else {
                    // haven't found the match yet, just continue to look
                    continue;
                }
            }
        }

        return;

    } // end modify (data column) function
    
    public double count( String [][] cl ) {

        int num = 1;        
        int len = cl.length;
        int row;
        int curr;
        int prev;
        int n;

        int [] srt = new int[len];

        for( row = 0; row < len; row++ ) {
            /*
             * get all of the columns used
             * to define the classes
             */
            srt[row] = Integer.valueOf(cl[row][0]).intValue();
        }

        // sort the array of columns before counting
        Arrays.sort(srt);

        curr = srt[0];
        prev = curr;

        // start n at 0
        n = 0;

        for( row = 0; row < len; row++ ) {
            // curr class is the current row of srt
            curr = srt[row];
            /*
             * as soon as curr is different from
             * prev, we will stop to take the tally
             * then continue to count the number of
             * classes
             */
            if( curr == prev ) {
                /*
                 * found another one from the same class
                 * just add it to the tally
                 */
                n++;
            }
            else {
                /*
                 * time to take the tally
                 */
                num *= n;
                // make sure that prev always contains the last value
                prev = curr;
                // starting a new class so n should be at 1
                n = 1;
            }
        }

        /*
         * we've broken from the loop before
         * accounting for the last class
         * so multiply num by n to account for it
         * also, we're computing N while the number
         * of classes is N_SQR ... so return the sqrt
         */
        return( Math.sqrt((double)(num*n)) );

    } // end count function
    
    public double count2() {

        /*
         * use the following calculation for the hard max number of classes
         * use the square root if there is a need to be sure that you specify
         * a number that's below the theoretical maximum
         */
        double n = 1.0 - ROWS + Math.sqrt((2 * ROWS)*(ROWS + 1));

        /*
         * by the theory in "A Data Classification Methodology
         * Using the Random Cluster Model", the maximum number of
         * classes allowed is given by
         * N <= 1 - ROWS + Math.sqrt((2 * ROWS)*(ROWS + 1))
         * for a given number of rows in the population ROWS
         * this will be far too many default classes in most cases
         * so, we'll just take N_SQR = N and redefine N to be the sqrt
         * of the number above since the above is still satisfied
         */
        return(n);

    }
    
    public String replace( String s, String [][] av ) {

        int row;

        String str = null;

        for( row = 0; row < av.length; row++ ) {
            if( av[row][0].compareTo(s) == 0 ) {
                /*
                 * found the match for the string s
                 * get the numric value and break
                 * for the return
                 */
                str = av[row][1].trim();
                break;
            }
            else {
                /*
                 * haven't yet found the correct replacement
                 * so continue to look
                 */
                continue;
            }
        }

        return(str);

    } // end replace funcion
    
} // DataClassification definition
