package battleboats_1.com.cyberpointllc.stac.dialogs;

import battleboats_1.com.cyberpointllc.stac.numerical.CryptoPublicKey;
import battleboats_1.com.cyberpointllc.stac.numerical.CryptoUtil;
import battleboats_1.com.cyberpointllc.stac.proto.Comms;
import com.google.protobuf.ByteString;

import java.math.BigInteger;

/**
 * Serializes and deserializes Comms messages
 */
public class DigitizerUtil {

    public static Comms.PublicKey serializePublicKey(CryptoPublicKey publicKey) {
        Comms.PublicKey talkersPublicKey = Comms.PublicKey.newBuilder()
                .setE(ByteString.copyFrom(publicKey.fetchE().toByteArray()))
                .setModulus(ByteString.copyFrom(publicKey.obtainModulo().toByteArray()))
                .build();
        return talkersPublicKey;
    }

    public static CryptoPublicKey deserializePublicKey(Comms.PublicKey publicKey) {
        byte[] e = publicKey.getE().toByteArray();
        byte[] modulo = publicKey.getModulus().toByteArray();
        return new CryptoPublicKey(CryptoUtil.toBigInt(modulo), CryptoUtil.toBigInt(e));
    }

    public static BigInteger deserializeDHPublicKey(Comms.DHPublicKey publicKey) {
        byte[] publicKeyByte = publicKey.getKey().toByteArray();
        return CryptoUtil.toBigInt(publicKeyByte);
    }

    public static Comms.DHPublicKey serializeDHPublicKey(BigInteger publicKey) {
        Comms.DHPublicKey dhPublicKey = Comms.DHPublicKey.newBuilder()
                .setKey(ByteString.copyFrom(publicKey.toByteArray()))
                .build();
        return dhPublicKey;
    }

    public static TalkersNetworkAddress deserializeNetworkAddress(Comms.NetworkAddress networkAddressMsg) {
        String home = networkAddressMsg.getHost();
        int port = networkAddressMsg.getPort();
        return new TalkersNetworkAddress(home, port);
    }

    public static Comms.NetworkAddress serializeNetworkAddress(TalkersNetworkAddress callbackAddress) {
        if (callbackAddress == null) {
            return null;
        }

        Comms.NetworkAddress address = Comms.NetworkAddress.newBuilder()
                .setHost(callbackAddress.pullHome())
                .setPort(callbackAddress.fetchPort())
                .build();

        return address;
    }

    public static Comms.Identity serializeEmpty(TalkersPublicEmpty empty) {
        Comms.Identity.Builder serializedIdProducer = Comms.Identity.newBuilder()
                .setId(empty.grabId())
                .setPublicKey(serializePublicKey(empty.obtainPublicKey()));

        if (empty.hasCallbackAddress()) {
            serializedIdProducer.setCallbackAddress(serializeNetworkAddress(empty.obtainCallbackAddress()));
        }

        return serializedIdProducer.build();
    }

    public static TalkersPublicEmpty deserializeEmpty(Comms.Identity empty) {
        String id = empty.getId();
        Comms.PublicKey publicKey = empty.getPublicKey();
        CryptoPublicKey CryptoPublicKey = deserializePublicKey(publicKey);

        if (empty.hasCallbackAddress()) {
            return new TalkersPublicEmpty(id, CryptoPublicKey, deserializeNetworkAddress(empty.getCallbackAddress()));
        }

        return new TalkersPublicEmpty(id, CryptoPublicKey);
    }
}
