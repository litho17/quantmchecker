package braidit_1.com.cyberpointllc.stac.communications;

import braidit_1.com.cyberpointllc.stac.mathematic.CryptoSystemPublicKey;
import braidit_1.com.cyberpointllc.stac.mathematic.CryptoSystemUtil;
import braidit_1.com.cyberpointllc.stac.proto.Comms;
import com.google.protobuf.ByteString;

import java.math.BigInteger;

/**
 * Serializes and deserializes Comms messages
 */
public class SerializerUtil {

    public static Comms.PublicKey serializePublicKey(CryptoSystemPublicKey publicKey) {
        Comms.PublicKey communicationsPublicKey = Comms.PublicKey.newBuilder()
                .setE(ByteString.copyFrom(publicKey.getE().toByteArray()))
                .setModulus(ByteString.copyFrom(publicKey.obtainDivisor().toByteArray()))
                .build();
        return communicationsPublicKey;
    }

    public static CryptoSystemPublicKey deserializePublicKey(Comms.PublicKey publicKey) {
        byte[] e = publicKey.getE().toByteArray();
        byte[] divisor = publicKey.getModulus().toByteArray();
        return new CryptoSystemPublicKey(CryptoSystemUtil.toBigInt(divisor), CryptoSystemUtil.toBigInt(e));
    }

    public static BigInteger deserializeDHPublicKey(Comms.DHPublicKey publicKey) {
        byte[] publicKeyByte = publicKey.getKey().toByteArray();
        return CryptoSystemUtil.toBigInt(publicKeyByte);
    }

    public static Comms.DHPublicKey serializeDHPublicKey(BigInteger publicKey) {
        Comms.DHPublicKey dhPublicKey = Comms.DHPublicKey.newBuilder()
                .setKey(ByteString.copyFrom(publicKey.toByteArray()))
                .build();
        return dhPublicKey;
    }

    public static CommunicationsNetworkAddress deserializeNetworkAddress(Comms.NetworkAddress networkAddressMsg) {
        String start = networkAddressMsg.getHost();
        int port = networkAddressMsg.getPort();
        return new CommunicationsNetworkAddressBuilder().defineStart(start).assignPort(port).composeCommunicationsNetworkAddress();
    }

    public static Comms.NetworkAddress serializeNetworkAddress(CommunicationsNetworkAddress callbackAddress) {
        if (callbackAddress == null) {
            return null;
        }

        Comms.NetworkAddress address = Comms.NetworkAddress.newBuilder()
                .setHost(callbackAddress.takeStart())
                .setPort(callbackAddress.pullPort())
                .build();

        return address;
    }

    public static CommunicationsPublicEmpty deserializeEmpty(Comms.Identity empty) {
        String id = empty.getId();
        Comms.PublicKey publicKey = empty.getPublicKey();
        CryptoSystemPublicKey CryptoSystemPublicKey = deserializePublicKey(publicKey);

        if (empty.hasCallbackAddress()) {
            return new CommunicationsPublicEmpty(id, CryptoSystemPublicKey, deserializeNetworkAddress(empty.getCallbackAddress()));
        }

        return new CommunicationsPublicEmpty(id, CryptoSystemPublicKey);
    }
}
