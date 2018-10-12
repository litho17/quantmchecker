package calculator_1.com.cyberpointllc.stac.netcontroller;

import com.sun.net.httpserver.HttpServer;
import com.sun.net.httpserver.HttpsConfigurator;
import com.sun.net.httpserver.HttpsParameters;
import com.sun.net.httpserver.HttpsServer;

import javax.net.ssl.KeyManagerFactory;
import javax.net.ssl.SSLContext;
import javax.net.ssl.SSLEngine;
import javax.net.ssl.SSLParameters;
import java.io.IOException;
import java.io.InputStream;
import java.net.InetSocketAddress;
import java.security.GeneralSecurityException;
import java.security.KeyStore;
import java.security.SecureRandom;
import java.util.concurrent.Executors;

/**
 * Creates an HTTP/S server which can be used to serve things.
 */
public class NetControllerFactory {
    public static HttpServer composeController(int port, InputStream resourceStream, String resourcePassword) throws IOException, GeneralSecurityException {
        if( resourceStream == null)
            return composeHttpController(port);
        else
            return composeHttpsController(port, resourceStream, resourcePassword);
    }

    private static HttpServer composeHttpController(int port) throws IOException {
        return( HttpServer.create(new InetSocketAddress(port), 0) );
    }

    private static HttpsServer composeHttpsController(int port, InputStream resourceStream, String resourcePassword) throws IOException, GeneralSecurityException {
        SSLContext sslContext = composeContext(resourceStream, resourcePassword.toCharArray());

        HttpsServer controller = HttpsServer.create(new InetSocketAddress(port), 0);

        controller.setHttpsConfigurator(new HttpsConfigurator(sslContext) {
            @Override
            public void configure(HttpsParameters params) {
                // we're going to force the use of only one crypto suite to make sure
                // we get consistent results
                try {
                    // initialise the SSL context
                    SSLContext c = SSLContext.getDefault();
                    SSLEngine engine = c.createSSLEngine();
                    String[] suites = {"TLS_RSA_WITH_AES_128_CBC_SHA256"};
                    params.setCipherSuites(suites);
                    params.setProtocols(engine.getEnabledProtocols());

                    // get the default parameters
                    SSLParameters defaultSSLParameters = c.getDefaultSSLParameters();
                    params.setSSLParameters(defaultSSLParameters);
                } catch (Exception ex) {
                    ex.printStackTrace();
                }
            }
        });

        controller.setExecutor(Executors.newCachedThreadPool());

        return controller;
    }

    private static SSLContext composeContext(InputStream inputStream, char[] password) throws IOException, GeneralSecurityException {
        // Initialise the keystore
        KeyStore ks = KeyStore.getInstance("JKS");
        ks.load(inputStream, password);

        // Setup the key manager factory
        KeyManagerFactory kmf = KeyManagerFactory.getInstance("SunX509");
        kmf.init(ks, password);

        // Setup the HTTPS context and parameters
        SSLContext sslContext = SSLContext.getInstance("TLS");
        sslContext.init(kmf.getKeyManagers(), null, new SecureRandom());

        return sslContext;
    }
}
