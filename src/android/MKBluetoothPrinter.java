
package cn.sj.cordova.bluetoothprint;

import android.annotation.SuppressLint;
import android.app.Activity;
import android.bluetooth.BluetoothAdapter;
import android.bluetooth.BluetoothDevice;
import android.bluetooth.BluetoothManager;
import android.bluetooth.BluetoothSocket;
import android.content.Context;
import android.content.SharedPreferences;
import android.content.pm.PackageManager;
import android.graphics.Bitmap;
import android.graphics.BitmapFactory;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Rect;
import android.os.Build;
import android.util.Base64;

import org.apache.cordova.CallbackContext;
import org.apache.cordova.CordovaInterface;
import org.apache.cordova.CordovaPlugin;
import org.apache.cordova.CordovaWebView;
import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.UnsupportedEncodingException;
import java.nio.charset.Charset;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.UUID;

// import android.content.ServiceConnection;
// import android.content.ComponentName;
// import android.content.Context;
// import android.content.Intent;
// import android.os.Bundle;
// import android.os.IBinder;
// import android.content.ContextWrapper;
// import android.os.RemoteException;
// import android.view.ContextThemeWrapper;


/**
 * Cordova plugin that prints receipts on Bluetooth ESC/POS thermal printers.
 *
 * <p>The plugin talks to a paired printer over a classic Bluetooth (RFCOMM / SPP)
 * socket and sends raw ESC/POS commands. It supports text, multi-column text
 * (2, 3 and 4 columns), Code-128 barcodes, QR codes, bitmap images, separator
 * lines and paper cutting.</p>
 *
 * <h2>Supported Cordova actions</h2>
 * <table border="1">
 *   <caption>Actions exposed to JavaScript</caption>
 *   <tr><th>Action</th><th>Description</th></tr>
 *   <tr><td>{@code autoConnectPeripheral}</td><td>Reconnect to the last used printer.</td></tr>
 *   <tr><td>{@code setPrinterPageWidth}</td><td>Set paper width ("58" or other, treated as 80 mm).</td></tr>
 *   <tr><td>{@code getCurrentSetPageWidth}</td><td>Get the paper width currently configured.</td></tr>
 *   <tr><td>{@code isConnectPeripheral}</td><td>Check whether a printer is connected.</td></tr>
 *   <tr><td>{@code scanForPeripherals} / {@code getPeripherals}</td><td>List paired Bluetooth devices.</td></tr>
 *   <tr><td>{@code stopScan}</td><td>Stop the continuous device lookup.</td></tr>
 *   <tr><td>{@code connectPeripheral}</td><td>Connect to a printer by MAC address.</td></tr>
 *   <tr><td>{@code setPrinterInfoAndPrinter}</td><td>Print a JSON list of print items.</td></tr>
 *   <tr><td>{@code stopPeripheralConnection}</td><td>Disconnect from the printer.</td></tr>
 *   <tr><td>{@code printLog}</td><td>Reserved (no-op).</td></tr>
 * </table>
 *
 * <h2>Print item JSON format</h2>
 * <p>{@code setPrinterInfoAndPrinter} receives a JSON array. Each element is an object with:</p>
 * <ul>
 *   <li>{@code infoType} - item type: 0 = text, 1 = text list (columns), 2 = barcode,
 *       3 = QR code, 4 = image (Base64), 5 = separator line, 6 = blank line,
 *       7 = footer text, 8 = cut paper</li>
 *   <li>{@code text} - text, barcode/QR content, or Base64 image data</li>
 *   <li>{@code textArray} - column values for {@code infoType} 1 (2, 3 or 4 entries)</li>
 *   <li>{@code fontType} - font size, see {@code FONT_*_NEW} constants</li>
 *   <li>{@code aligmentType} - alignment, see {@code ALIGN_*_NEW} constants</li>
 *   <li>{@code isTitle} - 1 prints the item in bold</li>
 *   <li>{@code maxWidth}, {@code qrCodeSize} - parsed but currently unused</li>
 * </ul>
 *
 * <p><b>Note:</b> the callback messages returned to JavaScript are in Chinese
 * (for example connection success / failure). They are kept unchanged so that
 * existing JavaScript code comparing those strings keeps working.</p>
 */
public class MKBluetoothPrinter extends CordovaPlugin {

    private BluetoothAdapter mBluetoothAdapter;

    /**
     * Runtime permission required on Android 12 (API 31) and newer to talk to
     * paired Bluetooth devices. Declared as a string so the plugin still compiles
     * against older compile SDKs.
     */
    private static final String BLUETOOTH_CONNECT = "android.permission.BLUETOOTH_CONNECT";

    private static final int REQUEST_BLUETOOTH_CONNECT = 7301;

    /**
     * All actions handled by {@link #execute(String, JSONArray, CallbackContext)}.
     */
    private static final List<String> ACTIONS = Arrays.asList(
            "autoConnectPeripheral", "setPrinterPageWidth", "getCurrentSetPageWidth",
            "isConnectPeripheral", "scanForPeripherals", "stopScan", "getPeripherals",
            "connectPeripheral", "setPrinterInfoAndPrinter", "stopPeripheralConnection",
            "printLog");

    /**
     * Actions that need {@code BLUETOOTH_CONNECT} on Android 12+.
     */
    private static final List<String> CONNECT_PERMISSION_ACTIONS = Arrays.asList(
            "autoConnectPeripheral", "scanForPeripherals", "getPeripherals", "connectPeripheral");

    // Call waiting for the user to answer the permission dialog
    private String pendingAction;
    private JSONArray pendingArgs;
    private CallbackContext pendingCallback;

    private Activity activity;
    private String boothAddress = "";
    private String oneModel, drawingRev, oneClass, oneCode, chipId, dateTime, specification = "";

    /**
     * Whether a Bluetooth printer is currently connected.
     */
    private static volatile boolean isConnection = false;//蓝牙是否连接

    /**
     * Whether device lookup keeps polling until paired devices are found.
     */
    private volatile boolean isKeep = false;//蓝牙持续回调
    private BluetoothDevice device = null;
    private static BluetoothSocket bluetoothSocket = null;
    private static OutputStream outputStream = null;

    /**
     * Standard Serial Port Profile (SPP) UUID used for RFCOMM connections.
     */
    private static final UUID uuid = UUID
            .fromString("00001101-0000-1000-8000-00805F9B34FB");

    /**
     * MAC address of the connected printer (returned to JavaScript as "uuid").
     */
    private static String uuid_bl = "";

    /**
     * Name of the connected printer.
     */
    private static String name_bl = "";

    /**
     * 复位打印机
     */
    /**
     * ESC/POS: initialize (reset) the printer.
     */
    public static final byte[] RESET = {0x1b, 0x40};

    /**
     * 左对齐
     */
    /**
     * ESC/POS: align left.
     */
    public static final byte[] ALIGN_LEFT = {0x1b, 0x61, 0x00};

    /**
     * 中间对齐
     */
    /**
     * ESC/POS: align center.
     */
    public static final byte[] ALIGN_CENTER = {0x1b, 0x61, 0x01};

    /**
     * 右对齐
     */
    /**
     * ESC/POS: align right.
     */
    public static final byte[] ALIGN_RIGHT = {0x1b, 0x61, 0x02};

    /**
     * 选择加粗模式
     */
    /**
     * ESC/POS: turn bold mode on.
     */
    public static final byte[] BOLD = {0x1b, 0x45, 0x01};

    /**
     * 取消加粗模式
     */
    /**
     * ESC/POS: turn bold mode off.
     */
    public static final byte[] BOLD_CANCEL = {0x1b, 0x45, 0x00};

    /**
     * 宽高加倍
     */
    /**
     * ESC/POS: double character width and height.
     */
    public static final byte[] DOUBLE_HEIGHT_WIDTH = {0x1d, 0x21, 0x11};

    /**
     * 宽加倍
     */
    /**
     * ESC/POS: double character width.
     */
    public static final byte[] DOUBLE_WIDTH = {0x1d, 0x21, 0x10};

    /**
     * 高加倍
     */
    /**
     * ESC/POS: double character height.
     */
    public static final byte[] DOUBLE_HEIGHT = {0x1d, 0x21, 0x01};

    /**
     * 字体不放大
     */
    /**
     * ESC/POS: normal character size (no enlargement).
     */
    public static final byte[] NORMAL = {0x1d, 0x21, 0x00};

    /**
     * 设置默认行间距
     */
    /**
     * ESC/POS: set the default line spacing.
     */
    public static final byte[] LINE_SPACING_DEFAULT = {0x1b, 0x32};

    /**
     * 打印纸一行最大的字节
     */
    /**
     * Maximum number of characters (bytes) that fit on one printed line.
     * 32 for 58 mm paper, 48 for wider paper (80 mm). Changed by
     * {@link #setPrinterPageWidth(JSONArray, CallbackContext)}.
     */
    private static int LINE_BYTE_SIZE = 48;


    // 对齐方式
    // ---- Alignment values (used in the "aligmentType" JSON field) ----

    /**
     * Alignment: left.
     */
    public static final int ALIGN_LEFT_NEW = 0;     // 靠左

    /**
     * Alignment: center.
     */
    public static final int ALIGN_CENTER_NEW = 1;   // 居中

    /**
     * Alignment: right.
     */
    public static final int ALIGN_RIGHT_NEW = 2;    // 靠右

    //字体大小
    // ---- Font size values (used in the "fontType" JSON field) ----

    /**
     * Font size: normal (1x width, 1x height).
     */
    public static final int FONT_NORMAL_NEW = 0;    // 正常

    /**
     * Font size: medium (1x width, 2x height).
     */
    public static final int FONT_MIDDLE_NEW = 1;    // 中等

    /**
     * Font size: big (2x width, 2x height).
     */
    public static final int FONT_BIG_NEW = 2;       // 大

    /**
     * Font size 3: 2x width, 1x height.
     */
    public static final int FONT_BIG_NEW3 = 3;    // 字体3

    /**
     * Font size 4: 1x width, 3x height.
     */
    public static final int FONT_BIG_NEW4 = 4;       // 字体4

    /**
     * Font size 5: 3x width, 2x height.
     */
    public static final int FONT_BIG_NEW5 = 5;    // 字体5

    /**
     * Font size 6: 3x width, 3x height.
     */
    public static final int FONT_BIG_NEW6 = 6;       // 字体6

    /**
     * Font size 7: 4x width, 4x height.
     */
    public static final int FONT_BIG_NEW7 = 7;    // 字体7

    /**
     * Font size 8: 5x width, 5x height.
     */
    public static final int FONT_BIG_NEW8 = 8;       // 字体8

    //加粗模式
    // ---- Bold mode values ----

    /**
     * Bold mode: bold on.
     */
    public static final int FONT_BOLD_NEW = 0;              // 字体加粗

    /**
     * Bold mode: bold off.
     */
    public static final int FONT_BOLD_CANCEL_NEW = 1;       // 取消加粗

    /**
     * Called by Cordova when the plugin is created. Stores the host activity.
     *
     * @param cordova the Cordova interface
     * @param webView the Cordova web view
     */
    @Override
    public void initialize(CordovaInterface cordova, CordovaWebView webView) {
        super.initialize(cordova, webView);

        activity = cordova.getActivity();

    }

    /**
     * Entry point for calls coming from JavaScript. Dispatches the action to the
     * matching method.
     *
     * @param action          action name (see the class documentation)
     * @param args            arguments passed from JavaScript
     * @param callbackContext callback used to return the result to JavaScript
     * @return {@code true} if the action is known and handled, {@code false} otherwise
     * @throws JSONException if the arguments cannot be parsed
     */
    public boolean execute(final String action, final JSONArray args, final CallbackContext callbackContext) throws JSONException {
        if (!ACTIONS.contains(action)) {
            return false;
        }

        // Android 12+ (API 31): BLUETOOTH_CONNECT is a runtime permission
        if (CONNECT_PERMISSION_ACTIONS.contains(action) && !hasConnectPermission()) {
            if (pendingCallback != null) {
                pendingCallback.error("Bluetooth permission request was superseded");
            }
            pendingAction = action;
            pendingArgs = args;
            pendingCallback = callbackContext;
            cordova.requestPermission(this, REQUEST_BLUETOOTH_CONNECT, BLUETOOTH_CONNECT);
            return true;
        }

        runAction(action, args, callbackContext);
        return true;
    }

    /**
     * Whether the app may use paired Bluetooth devices. Always true below Android 12.
     */
    private boolean hasConnectPermission() {
        return Build.VERSION.SDK_INT < 31 || cordova.hasPermission(BLUETOOTH_CONNECT);
    }

    /**
     * Runs an action on the Cordova thread pool. Connecting, printing and the
     * paired-device polling block, so they must not run on the WebView thread.
     */
    private void runAction(final String action, final JSONArray args, final CallbackContext callbackContext) {
        cordova.getThreadPool().execute(new Runnable() {
            @Override
            public void run() {
                try {
                    dispatch(action, args, callbackContext);
                } catch (Exception e) {
                    e.printStackTrace();
                    callbackContext.error(String.valueOf(e.getMessage()));
                }
            }
        });
    }

    /**
     * Continues the call that was waiting for the Bluetooth permission dialog.
     */
    @Override
    public void onRequestPermissionResult(int requestCode, String[] permissions, int[] grantResults) throws JSONException {
        if (requestCode != REQUEST_BLUETOOTH_CONNECT || pendingCallback == null) {
            return;
        }
        String action = pendingAction;
        JSONArray args = pendingArgs;
        CallbackContext callbackContext = pendingCallback;
        pendingAction = null;
        pendingArgs = null;
        pendingCallback = null;

        if (grantResults.length > 0 && grantResults[0] == PackageManager.PERMISSION_GRANTED) {
            runAction(action, args, callbackContext);
        } else {
            callbackContext.error("Bluetooth permission denied");
        }
    }

    private void dispatch(String action, JSONArray args, CallbackContext callbackContext) throws JSONException {
        if (action.equals("autoConnectPeripheral")) {
            // Auto-connect to a previously connected device
            autoConnect(args, callbackContext);
        } else if (action.equals("setPrinterPageWidth")) {
            // Set printer paper width
            setPrinterPageWidth(args, callbackContext);
        } else if (action.equals("getCurrentSetPageWidth")) {
            // Get the currently configured paper width
            getCurrentSetPageWidth(args, callbackContext);
        } else if (action.equals("isConnectPeripheral")) {
            // Is a device connected? Returns "1": yes, "0": no
            isConnectPeripheral(args, callbackContext);
        } else if (action.equals("scanForPeripherals") || action.equals("getPeripherals")) {
            // List paired Bluetooth devices.
            // keep: keep polling until devices are found (0: no, 1: yes, default: 0)
            // Result example: [{"name":"Printer_2EC1","uuid":"9A87E98E-BE88-5BA6-2C31-ED4869300E6E"}]
            getPairedDevices(args, callbackContext);
        } else if (action.equals("stopScan")) {
            // Stop scanning
            stopScan(args, callbackContext);
        } else if (action.equals("connectPeripheral")) {
            // Connect to the selected Bluetooth device (printer)
            connectDevice(args, callbackContext);
        } else if (action.equals("setPrinterInfoAndPrinter")) {
            // Print
            printText(args, callbackContext);
        } else if (action.equals("stopPeripheralConnection")) {
            // Disconnect
            closeConnect(args, callbackContext);
        } else if (action.equals("printLog")) {
            // Print a log message (iOS: Xcode console; no-op on Android)
            printLog(args, callbackContext);
        }
    }

    /**
     * Returns the default Bluetooth adapter, or {@code null} if the device has no Bluetooth.
     */
    private BluetoothAdapter getAdapter() {
        BluetoothManager manager = (BluetoothManager) cordova.getActivity().getSystemService(Context.BLUETOOTH_SERVICE);
        BluetoothAdapter adapter = manager != null ? manager.getAdapter() : null;
        return adapter != null ? adapter : BluetoothAdapter.getDefaultAdapter();
    }

    /**
     * Closes any previous socket, opens an RFCOMM socket to the device and
     * remembers the address for {@link #autoConnect}. Throws on failure.
     */
    private void openSocket(BluetoothDevice target) throws IOException {
        closeQuietly();
        BluetoothSocket socket = target.createRfcommSocketToServiceRecord(uuid);
        try {
            socket.connect();
            outputStream = socket.getOutputStream();
        } catch (IOException e) {
            try {
                socket.close();
            } catch (IOException ignored) {
            }
            throw e;
        }
        bluetoothSocket = socket;
        device = target;
        name_bl = target.getName();
        uuid_bl = target.getAddress();
        isConnection = true;
        activity.getSharedPreferences("device", Context.MODE_PRIVATE)
                .edit().putString("address", uuid_bl).apply();
    }

    private static void closeQuietly() {
        isConnection = false;
        try {
            if (outputStream != null) {
                outputStream.close();
            }
        } catch (IOException ignored) {
        }
        try {
            if (bluetoothSocket != null) {
                bluetoothSocket.close();
            }
        } catch (IOException ignored) {
        }
        outputStream = null;
        bluetoothSocket = null;
    }

    /**
     * Reconnects to the last used printer. The MAC address is read from the
     * {@code "device"} SharedPreferences (key {@code "address"}) and matched against
     * the list of bonded devices.
     *
     * <p>Callback: success ("connection successful") or error ("connection failed").</p>
     *
     * @param args            unused
     * @param callbackContext callback to return the result
     */
    public synchronized void autoConnect(final JSONArray args, final CallbackContext callbackContext) {
        if (isConnection) {
            callbackContext.success("连接成功");
            return;
        }
        SharedPreferences pref = activity.getSharedPreferences("device", Context.MODE_PRIVATE);
        String deviceAddress = pref.getString("address", "");
        mBluetoothAdapter = getAdapter();
        if (deviceAddress == null || deviceAddress.isEmpty()
                || mBluetoothAdapter == null || !mBluetoothAdapter.isEnabled()) {
            callbackContext.error("连接失败");
            return;
        }
        try {
            BluetoothDevice saved = null;
            for (BluetoothDevice device1 : mBluetoothAdapter.getBondedDevices()) {// 获取本机已配对设备
                if (device1.getAddress().equals(deviceAddress)) {
                    saved = device1;
                    break;
                }
            }
            if (saved == null) {
                callbackContext.error("连接失败");
                return;
            }
            openSocket(saved);
            callbackContext.success("连接成功");
        } catch (Exception e) {
            isConnection = false;
            callbackContext.error("连接失败");
        }
    }

    /*
     *设置打印机宽度
     */

    /**
     * Sets the printer paper width.
     *
     * <p>The first argument is the width in millimetres as a string. {@code "58"}
     * sets {@link #LINE_BYTE_SIZE} to 32 characters per line; any other value
     * sets it to 48 characters per line.</p>
     *
     * <p>Callback: success {@code "0"} on success, success {@code "1"} on failure.</p>
     *
     * @param args            {@code args[0]} = paper width, for example "58" or "80"
     * @param callbackContext callback to return the result
     * @throws JSONException if the arguments cannot be parsed
     */
    public void setPrinterPageWidth(final JSONArray args, final CallbackContext callbackContext) throws JSONException {
        String size = "78";
        try {
            size = args.getString(0);
            if ("58".equals(size)) {
                LINE_BYTE_SIZE = 32;
            } else {
                LINE_BYTE_SIZE = 48;
            }
            callbackContext.success("0");
        } catch (Exception e) {
            e.printStackTrace();
            callbackContext.success("1");
        }
    }

    /*
     *获取当前设置的纸张宽度
     */

    /**
     * Returns the paper width currently configured.
     *
     * <p>Callback: success {@code "58"} if the line size is 32 characters,
     * otherwise {@code "78"}.</p>
     *
     * @param args            unused
     * @param callbackContext callback to return the result
     * @throws JSONException if the arguments cannot be parsed
     */
    public void getCurrentSetPageWidth(final JSONArray args, final CallbackContext callbackContext) throws JSONException {
        String size = "78";

        if (LINE_BYTE_SIZE == 32) {
            size = "58";
        }
        callbackContext.success(size);

    }
    /*
     *是否已连接设备   * 返回： "1":是  "0":否
     */

    /**
     * Checks whether a printer is connected.
     *
     * <p>Callback: if connected, a JSON array with one object
     * {@code [{"name": ..., "uuid": ...}]} describing the printer; otherwise
     * the string {@code "0"}.</p>
     *
     * @param args            unused
     * @param callbackContext callback to return the result
     * @throws JSONException if the result JSON cannot be built
     */
    public void isConnectPeripheral(final JSONArray args, final CallbackContext callbackContext) throws JSONException {
        if (isConnection) {
            JSONArray json = new JSONArray();
            JSONObject jo = new JSONObject();
            jo.put("name", name_bl);
            jo.put("uuid", uuid_bl);
            json.put(jo);
            callbackContext.success(json);
        } else {
            callbackContext.success("0");
        }
    }

    /**
     * Reserved for logging from JavaScript. Currently does nothing on Android.
     *
     * @param args            unused
     * @param callbackContext unused
     */
    private void printLog(JSONArray args, CallbackContext callbackContext) {

    }

    /**
     * Closes the Bluetooth socket and output stream and marks the printer as
     * disconnected.
     *
     * <p>Callback: success ("disconnected") or error ("disconnect failed").</p>
     *
     * @param args            unused
     * @param callbackContext callback to return the result
     * @throws JSONException if the arguments cannot be parsed
     */
    private synchronized void closeConnect(final JSONArray args, final CallbackContext callbackContext) throws JSONException {
        closeQuietly();
        callbackContext.success("断开连接成功！");
    }

    /**
     * Connects to a Bluetooth printer by MAC address using an RFCOMM socket.
     * If a connection already exists, it simply reports success.
     *
     * <p>Callback: success ("connection successful") or error ("connection failed").</p>
     *
     * @param args            {@code args[0]} = Bluetooth MAC address of the printer
     * @param callbackContext callback to return the result
     * @throws JSONException if the address argument is missing
     */
    private synchronized void connectDevice(final JSONArray args, final CallbackContext callbackContext) throws JSONException {
        final String address = args.getString(0);
        if (isConnection) {//连接了
            callbackContext.success("连接成功");
            return;
        }
        // Get the local Bluetooth adapter
        mBluetoothAdapter = getAdapter();
        if (mBluetoothAdapter == null || !mBluetoothAdapter.isEnabled()) {
            callbackContext.error("连接失败");
            return;
        }
        try {
            openSocket(mBluetoothAdapter.getRemoteDevice(address));
            callbackContext.success("连接成功");
        } catch (Exception e) {
            isConnection = false;
            callbackContext.error("连接失败");
        }
    }

    /*
     *获取已配对的蓝牙设备 keep：是否持续回调 （0：否， 1：是，default:0） 开始扫描设备 [{"name":"Printer_2EC1","uuid":"9A87E98E-BE88-5BA6-2C31-ED4869300E6E"}]
     */

    /**
     * Returns the list of Bluetooth devices already paired with the phone.
     *
     * <p>If {@code keep} is {@code "1"}, the method keeps polling until at least
     * one paired device exists (it blocks until then, or until {@link #stopScan}
     * clears the flag).</p>
     *
     * <p>Callback: success with a JSON array such as
     * {@code [{"name":"Printer_2EC1","uuid":"9A87E98E-BE88-5BA6-2C31-ED4869300E6E"}]};
     * error ("no paired Bluetooth device") if the list is empty.</p>
     *
     * @param args            {@code args[0]} (optional) = keep polling flag, "0" or "1" (default "0")
     * @param callbackContext callback to return the result
     * @throws JSONException if the result JSON cannot be built
     */
    private void getPairedDevices(final JSONArray args, final CallbackContext callbackContext) throws JSONException {
        String keep = "0";
        try {
            keep = args.getString(0);
        } catch (Exception e) {
            e.printStackTrace();
        }
        isKeep = "1".equals(keep);

        Set<BluetoothDevice> pairedDevices = null;
        try {
            do {
                // Get the local Bluetooth adapter
                mBluetoothAdapter = getAdapter();
                if (mBluetoothAdapter != null && mBluetoothAdapter.isEnabled()) {
                    pairedDevices = mBluetoothAdapter.getBondedDevices();
                }
                if (pairedDevices != null && pairedDevices.size() > 0) {
                    break;
                }
                if (isKeep) {
                    Thread.sleep(500);
                }
            } while (isKeep);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        } catch (SecurityException e) {
            callbackContext.error("Bluetooth permission denied");
            return;
        }

        if (pairedDevices != null && pairedDevices.size() > 0) {
            JSONArray json = new JSONArray();
            for (BluetoothDevice device : pairedDevices) {
                JSONObject jo = new JSONObject();
                jo.put("name", device.getName());
                jo.put("uuid", device.getAddress());
                json.put(jo);
            }
            callbackContext.success(json);
        } else {
            callbackContext.error("未有配对蓝牙");
        }
    }

    /*
     * 停止扫描
     */

    /**
     * Stops the continuous paired-device lookup started with {@code keep = "1"}.
     *
     * <p>Callback: success ("scan stopped").</p>
     *
     * @param args            unused
     * @param callbackContext callback to return the result
     * @throws JSONException if the arguments cannot be parsed
     */
    private void stopScan(final JSONArray args, final CallbackContext callbackContext) throws JSONException {
        // Get the local Bluetooth adapter
        isKeep = false;
        callbackContext.success("停止扫描成功");

    }

    /**
     * Prints a list of print items.
     *
     * <p>{@code args[0]} is a JSON array string. Each element is passed to
     * {@link #sendprint(JSONObject)}. For 58 mm paper, five blank lines are
     * added at the end so the printed content clears the cutter. A paper cut
     * command is then sent.</p>
     *
     * <p>Callback: success ("print successful"), or error ("print failed" plus the
     * exception message), or error ("device not connected, please reconnect").</p>
     *
     * @param args            {@code args[0]} = JSON array string of print items
     * @param callbackContext callback to return the result
     * @throws JSONException if the first argument is missing
     */
    private synchronized void printText(final JSONArray args, final CallbackContext callbackContext) throws JSONException {

        String sendData = args.getString(0);

        if (isConnection) {
            try {
                if (sendData != null && !"".equals(sendData)) {


                    JSONArray top_array = new JSONArray(sendData);

                    if (top_array != null && top_array.length() > 0) {
                        for (int m = 0; m < top_array.length(); m++) {
                            JSONObject jsonData = (JSONObject) top_array.get(m);
                            sendprint(jsonData);
                        }
                    }

                    if (LINE_BYTE_SIZE == 32) {
                        MKBluetoothPrinter.printText("\n");
                        MKBluetoothPrinter.printText("\n");
                        MKBluetoothPrinter.printText("\n");
                        MKBluetoothPrinter.printText("\n");
                        MKBluetoothPrinter.printText("\n");
                    }
                    //结束循环时
                    MKBluetoothPrinter.selectCommand(MKBluetoothPrinter.getCutPaperCmd());
//                     JSONObject dataJson = new JSONObject(sendData);
//                   ///获取globalDatatop数据
//                   JSONArray top_array = dataJson.optJSONArray("globalDatatop");
//                   //获取globalDatafoot数据
//                   JSONArray foot_array = dataJson.optJSONArray("globalDatafoot");
//                   //获取personsData数据
//                   JSONArray persons_object = dataJson.optJSONArray("personsData");
//
//
//                    MKBluetoothPrinter.selectCommand(MKBluetoothPrinter.RESET);
//                   MKBluetoothPrinter.selectCommand(MKBluetoothPrinter.LINE_SPACING_DEFAULT);
//
//                   if (persons_object != null && persons_object.length() > 0) {
//                       for (int j = 0; j < persons_object.length(); j++) {
//                           JSONObject person = (JSONObject) persons_object.get(j);
//
//
//                           if(person!=null) {
//                               JSONArray person_arr = person.optJSONArray("person");
//                               if (person_arr != null && person_arr.length() > 0) {
//
//
//                                           //循环打印头部
//                                           if (top_array != null && top_array.length() > 0) {
//                                               for (int m = 0; m < top_array.length(); m++) {
//                                                   JSONObject jsonData = (JSONObject) top_array.get(m);
//                                                    sendprint(jsonData);
//                                               }
//                                           }
//                                           for (int n = 0; n < person_arr.length(); n++) {
//                                               JSONObject jsonData = (JSONObject) person_arr.get(n);
//                                               sendprint(jsonData);
//                                           }
//
//
//                                           //循环打印底部部
//                                           if (foot_array != null && foot_array.length() > 0) {
//                                               for (int h = 0; h < foot_array.length(); h++) {
//                                                   JSONObject jsonData = (JSONObject) foot_array.get(h);
//                                                    sendprint(jsonData);
//                                               }
//                                           }
//                                           MKBluetoothPrinter.printText("\n");
//                                           MKBluetoothPrinter.printText("\n");
//
//                                           //结束循环时
//                                           MKBluetoothPrinter.selectCommand(MKBluetoothPrinter.getCutPaperCmd());
//
//
//                               }
//                           }
//                       }
//                   }
                }
                callbackContext.success("打印成功！");
            } catch (Exception e) {
                e.printStackTrace();
                callbackContext.error("打印失败！" + e.getMessage());
            }
        } else {
            callbackContext.error("设备未连接，请重新连接！");
        }
    }

    /**
     * Prints a single print item described by a JSON object.
     *
     * <p>It first applies bold, alignment and font size, then prints according to
     * {@code infoType}: 0 = text, 1 = columns, 2 = barcode, 3 = QR code,
     * 4 = image, 5 = separator line, 6 = blank line, 7 = footer text,
     * 8 = cut paper. A newline is written after each item. Exceptions are
     * caught and logged, so one bad item does not stop the whole print job.</p>
     *
     * @param jsonData print item (see the class documentation for the fields)
     */
    public void sendprint(JSONObject jsonData) {


        try {
            System.out.println("jsonData:" + jsonData);
            int infoType = jsonData.optInt("infoType");
            String text = jsonData.optString("text");
            int fontType = jsonData.optInt("fontType");
            int aligmentType = jsonData.optInt("aligmentType");
            int isTitle = jsonData.optInt("isTitle");
            int maxWidth = jsonData.optInt("maxWidth");
            int qrCodeSize = jsonData.optInt("qrCodeSize");
            JSONArray textArray = jsonData.optJSONArray("textArray");

                                      /*  类型 infoType text= 0;          textList= 1;         barCode = 2;          qrCode = 3;
                                               image  = 4;         seperatorLine   = 5;            spaceLine       = 6;            footer          = 7;*/


            int fontType_int = fontType;
            int aligmentType_int = aligmentType;
            //                      int fontType_int =0;
            //                       int aligmentType_int =0;
            //                       try{
            //                           fontType_int =Integer.parseInt(fontType);
            //                       }catch (Exception e){
            //
            //                       }
            //
            //                       try{
            //                           aligmentType_int =Integer.parseInt(aligmentType);
            //                       }catch (Exception e){
            //
            //                       }

            if (isTitle == 1) {
                MKBluetoothPrinter.selectCommand(MKBluetoothPrinter.BOLD);
            } else {
                MKBluetoothPrinter.selectCommand(MKBluetoothPrinter.BOLD_CANCEL);
            }
            MKBluetoothPrinter.selectCommand(getAlignCmd(aligmentType_int));
            MKBluetoothPrinter.selectCommand(getFontSizeCmd(fontType_int));

            if (infoType == 0) {
                MKBluetoothPrinter.printText(text);
            } else if (infoType == 1) {
                if (textArray != null && textArray.length() > 0) {
                    if (textArray.length() == 2) {
                        MKBluetoothPrinter.printText(MKBluetoothPrinter.printTwoData(textArray.get(0).toString(), textArray.get(1).toString()));
                    } else if (textArray.length() == 3) {
                        MKBluetoothPrinter.printText(MKBluetoothPrinter.printThreeData(textArray.get(0).toString(), textArray.get(1).toString(), textArray.get(2).toString()));
                    } else if (textArray.length() == 4) {
                        MKBluetoothPrinter.printText(MKBluetoothPrinter.printFourData(textArray.get(0).toString(), textArray.get(1).toString(), textArray.get(2).toString(), textArray.get(3).toString()));
                    }
                }
            } else if (infoType == 2) {
                MKBluetoothPrinter.printText(getBarcodeCmd(text));
            } else if (infoType == 3) {
                // 发送二维码打印图片前导指令
                byte[] start = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1B,
                        0x40, 0x1B, 0x33, 0x00};
                MKBluetoothPrinter.selectCommand(start);
                MKBluetoothPrinter.selectCommand(getQrCodeCmd(text));
                // 发送结束指令
                byte[] end = {0x1d, 0x4c, 0x1f, 0x00};
                MKBluetoothPrinter.selectCommand(end);
            } else if (infoType == 4) {
                text = text.replace("data:image/jpeg;base64,", "").replace("data:image/png;base64,", "");


                /**获取打印图片的数据**/
                byte[] bitmapArray;
                bitmapArray = Base64.decode(text, Base64.DEFAULT);
                for (int n = 0; n < bitmapArray.length; ++n) {
                    if (bitmapArray[n] < 0) {// 调整异常数据
                        bitmapArray[n] += 256;
                    }

                }

                Bitmap bitmap = BitmapFactory.decodeByteArray(bitmapArray, 0, bitmapArray.length);


                bitmap = compressPic(bitmap);

                if (bitmap != null) {
                    //图片的长和框必须是大于24*size
                    byte[] draw2PxPoint = draw2PxPoint(bitmap);
                    //发送打印图片前导指令

                    MKBluetoothPrinter.selectCommand(draw2PxPoint);
                }

                //图片的长和框必须是大于24*size
                //  byte[] draw2PxPoint = PicFromPrintUtils.draw2PxPoint(bitmap);
                //发送打印图片前导指令

                // MKBluetoothPrinter.selectCommand(draw2PxPoint);


                //MKBluetoothPrinter.selectCommand(draw2PxPoint);
                //InputStream fin = Bitmap2IS(bitmap);
                //byte[] buffer = getReadBitMapBytes(bitmap);
                //发送打印图片前导指令
                //byte[] start = { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1B,
                //       0x40, 0x1B, 0x33, 0x00 };
                //  MKBluetoothPrinter.selectCommand(start);
                //MKBluetoothPrinter.selectCommandByte(buffer);
                // 发送结束指令
                //  byte[] end = { 0x1d, 0x4c, 0x1f, 0x00 };
                //  MKBluetoothPrinter.selectCommand(end);
                //MKBluetoothPrinter.selectCommand(bitmapArray);
                // 发送结束指令

            } else if (infoType == 5) {
                MKBluetoothPrinter.printText(printSeperatorLine());
            } else if (infoType == 6) {
                MKBluetoothPrinter.printText("\n");
            } else if (infoType == 7) {
                MKBluetoothPrinter.printText(text);
            } else if (infoType == 8) {
                //结束循环时
                MKBluetoothPrinter.selectCommand(MKBluetoothPrinter.getCutPaperCmd());
            }
            MKBluetoothPrinter.printText("\n");


        } catch (Exception e) {
            e.printStackTrace();
            ;
        }

    }

    /**
     * 对图片进行压缩（去除透明度）
     *
     * @param
     */
    /**
     * Redraws a bitmap onto a white background, removing transparency
     * (transparent pixels would otherwise print as black).
     *
     * @param bitmap source bitmap
     * @return a new opaque bitmap with the same size, or {@code null} if an error occurs
     */
    public static Bitmap compressPic(Bitmap bitmap) {
        Bitmap targetBmp = null;
        try {
            // 获取这个图片的宽和高
            int width = bitmap.getWidth();
            int height = bitmap.getHeight();
            // 指定调整后的宽度和高度
            //int newWidth = 240;
            // int newHeight = 240;
            int newWidth = bitmap.getWidth();
            int newHeight = bitmap.getHeight();
            targetBmp = Bitmap.createBitmap(newWidth, newHeight, Bitmap.Config.ARGB_8888);
            Canvas targetCanvas = new Canvas(targetBmp);
            targetCanvas.drawColor(0xffffffff);
            targetCanvas.drawBitmap(bitmap, new Rect(0, 0, width, height), new Rect(0, 0, newWidth, newHeight), null);
        } catch (Exception e) {

        }
        return targetBmp;
    }

    /**
     * 灰度图片黑白化，黑色是1，白色是0
     *
     * @param x   横坐标
     * @param y   纵坐标
     * @param bit 位图
     * @return
     */
    /**
     * Converts one pixel to a black/white bit. Black is 1 and white is 0
     * (gray value below 128 is treated as black).
     *
     * @param x   x coordinate
     * @param y   y coordinate
     * @param bit source bitmap
     * @return 1 for a black pixel, 0 for a white pixel or when the coordinates are out of range
     */
    public static byte px2Byte(int x, int y, Bitmap bit) {
        if (x < bit.getWidth() && y < bit.getHeight()) {
            byte b;
            int pixel = bit.getPixel(x, y);
            int red = (pixel & 0x00ff0000) >> 16; // 取高两位
            int green = (pixel & 0x0000ff00) >> 8; // 取中两位
            int blue = pixel & 0x000000ff; // 取低两位
            int gray = RGB2Gray(red, green, blue);
            if (gray < 128) {
                b = 1;
            } else {
                b = 0;
            }
            return b;
        }
        return 0;
    }

    /**
     * 图片灰度的转化
     */
    /**
     * Converts an RGB color to a gray level using the standard luminance formula
     * (0.299 R + 0.587 G + 0.114 B).
     *
     * @param r red (0-255)
     * @param g green (0-255)
     * @param b blue (0-255)
     * @return gray value (0-255)
     */
    private static int RGB2Gray(int r, int g, int b) {
        int gray = (int) (0.29900 * r + 0.58700 * g + 0.11400 * b);  //灰度转化公式
        return gray;
    }

/*************************************************************************
 * 假设一个240*240的图片，分辨率设为24, 共分10行打印
 * 每一行,是一个 240*24 的点阵, 每一列有24个点,存储在3个byte里面。
 * 每个byte存储8个像素点信息。因为只有黑白两色，所以对应为1的位是黑色，对应为0的位是白色
 **************************************************************************/
    /**
     * 把一张Bitmap图片转化为打印机可以打印的字节流
     *
     * @param bmp
     * @return
     */
    /*
     * Example: a 240x240 image printed at 24-dot resolution is sent as 10 strips.
     * Each strip is a 240x24 dot matrix: every column has 24 dots stored in
     * 3 bytes, and each byte holds 8 pixels. Because the image is monochrome,
     * a bit value of 1 is black and 0 is white.
     */

    /**
     * Converts a bitmap into an ESC/POS byte stream that the printer can print,
     * using the {@code ESC * 33} (24-dot double-density) bit-image command.
     *
     * <p>The image is printed in horizontal strips 24 pixels high. The output
     * buffer has 1000 extra bytes to cover the case where the image height is not
     * a multiple of 24 (the last strip is padded) and the command overhead.
     * The line spacing is set to 0 first so the strips join seamlessly.</p>
     *
     * @param bmp source bitmap
     * @return ESC/POS data ready to be sent to the printer
     */
    public static byte[] draw2PxPoint(Bitmap bmp) {
        //用来存储转换后的 bitmap 数据。为什么要再加1000，这是为了应对当图片高度无法
        //整除24时的情况。比如bitmap 分辨率为 240 * 250，占用 7500 byte，
        //但是实际上要存储11行数据，每一行需要 24 * 240 / 8 =720byte 的空间。再加上一些指令存储的开销，
        //所以多申请 1000byte 的空间是稳妥的，不然运行时会抛出数组访问越界的异常。
        int size = bmp.getWidth() * bmp.getHeight() / 8 + 1000;
        byte[] data = new byte[size];
        int k = 0;
        //设置行距为0的指令
        data[k++] = 0x1B;
        data[k++] = 0x33;
        data[k++] = 0x00;
        // 逐行打印
        for (int j = 0; j < bmp.getHeight() / 24f; j++) {
            //打印图片的指令
            data[k++] = 0x1B;
            data[k++] = 0x2A;
            data[k++] = 33;
            data[k++] = (byte) (bmp.getWidth() % 256); //nL
            data[k++] = (byte) (bmp.getWidth() / 256); //nH
            //对于每一行，逐列打印
            for (int i = 0; i < bmp.getWidth(); i++) {
                //每一列24个像素点，分为3个字节存储
                for (int m = 0; m < 3; m++) {
                    //每个字节表示8个像素点，0表示白色，1表示黑色
                    for (int n = 0; n < 8; n++) {
                        byte b = px2Byte(i, j * 24 + m * 8 + n, bmp);
                        data[k] += data[k] + b;
                    }
                    k++;
                }
            }
            data[k++] = 10;//换行
        }
        return data;
    }


    /**解析图片 获取打印数据**/
    /**
     * Converts a bitmap into 8-dot bit-image data ({@code ESC * 1}). Any pixel that
     * is not pure white is printed as black.
     *
     * <p><b>Note:</b> this method is currently not used and assumes a fixed image
     * width of 322 pixels.</p>
     *
     * @param bitmap source bitmap
     * @return the print data
     */
    private byte[] getReadBitMapBytes(Bitmap bitmap) {
        /***图片添加水印**/
        //bitmap = createBitmap(bitmap);
        byte[] bytes = null;  //打印数据
        int width = bitmap.getWidth();
        int height = bitmap.getHeight();
        System.out.println("width=" + width + ", height=" + height);
        int heightbyte = (height - 1) / 8 + 1;
        int bufsize = width * heightbyte;
        int m1, n1;
        byte[] maparray = new byte[bufsize];

        byte[] rgb = new byte[3];

        int[] pixels = new int[width * height]; //通过位图的大小创建像素点数组

        bitmap.getPixels(pixels, 0, width, 0, 0, width, height);
        /**解析图片 获取位图数据**/
        for (int j = 0; j < height; j++) {
            for (int i = 0; i < width; i++) {
                int pixel = pixels[width * j + i]; /**获取ＲＧＢ值**/
                int r = Color.red(pixel);
                int g = Color.green(pixel);
                int b = Color.blue(pixel);
                //System.out.println("i=" + i + ",j=" + j + ":(" + r + ","+ g+ "," + b + ")");
                rgb[0] = (byte) r;
                rgb[1] = (byte) g;
                rgb[2] = (byte) b;
                if (r != 255 || g != 255 || b != 255) {//如果不是空白的话用黑色填充    这里如果童鞋要过滤颜色在这里处理
                    m1 = (j / 8) * width + i;
                    n1 = j - (j / 8) * 8;
                    maparray[m1] |= (byte) (1 << 7 - ((byte) n1));
                }
            }
        }
        byte[] b = new byte[322];
        int line = 0;
        int j = 0;
        ByteArrayOutputStream baos = new ByteArrayOutputStream();

        /**对位图数据进行处理**/
        for (int i = 0; i < maparray.length; i++) {
            b[j] = maparray[i];
            j++;
            if (j == 322) {  /**  322图片的宽 **/
                if (line < ((322 - 1) / 8)) {
                    byte[] lineByte = new byte[329];
                    byte nL = (byte) 322;
                    byte nH = (byte) (322 >> 8);
                    int index = 5;
                    /**添加打印图片前导字符  每行的 这里是8位**/
                    lineByte[0] = 0x1B;
                    lineByte[1] = 0x2A;
                    lineByte[2] = 1;
                    lineByte[3] = nL;
                    lineByte[4] = nH;
                    /**copy 数组数据**/
                    System.arraycopy(b, 0, lineByte, index, b.length);

                    lineByte[lineByte.length - 2] = 0x0D;
                    lineByte[lineByte.length - 1] = 0x0A;
                    baos.write(lineByte, 0, lineByte.length);
                    try {
                        baos.flush();
                    } catch (IOException e) {
                        e.printStackTrace();
                    }
                    line++;
                }
                j = 0;
            }
        }
        bytes = baos.toByteArray();
        return bytes;
    }


    /**
     * Converts a bitmap to a PNG {@link InputStream}.
     *
     * <p>Currently not used.</p>
     *
     * @param bm source bitmap
     * @return an input stream with the PNG-encoded image
     */
    private static InputStream Bitmap2IS(Bitmap bm) {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        bm.compress(Bitmap.CompressFormat.PNG, 100, baos);
        InputStream sbs = new ByteArrayInputStream(baos.toByteArray());
        return sbs;
    }
    /**
     * 打印------------------------------------------------
     *
     *
     */
    /**
     * Builds a separator line made of {@code -} characters that spans the full
     * line width ({@link #LINE_BYTE_SIZE}).
     *
     * @return the separator string, for example 32 or 48 dashes
     */
    public static String printSeperatorLine() {
        String seperator = "";
        for (int i = 0; i < LINE_BYTE_SIZE; i++) {
            seperator += "-";
        }
        return seperator;
    }
    /**
     * 打印文字
     *
     * @param text 要打印的文字
     */
    /**
     * Sends text to the printer, encoded as GBK.
     *
     * @param text the text to print
     */
    public static void printText(String text) {
        try {
            byte[] data = text.getBytes("gbk");
            outputStream.write(data, 0, data.length);
            outputStream.flush();
        } catch (IOException e) {
            e.printStackTrace();
            isConnection = false;
        }
    }

    /**
     * 设置打印格式
     *
     * @param command 格式指令
     */
    /**
     * Sends a raw command to the printer using an explicit offset and length.
     *
     * @param command the command bytes
     */
    public static void selectCommandByte(byte[] command) {
        try {
            outputStream.write(command, 0, command.length);
            outputStream.flush();
        } catch (IOException e) {
            e.printStackTrace();
            isConnection = false;
        }
    }

    /**
     * 设置打印格式
     *
     * @param command 格式指令
     */
    /**
     * Sends a raw ESC/POS command (for example format, alignment, cut) to the printer.
     *
     * @param command the command bytes
     */
    public static void selectCommand(byte[] command) {
        try {
            outputStream.write(command);
            outputStream.flush();
        } catch (IOException e) {
            e.printStackTrace();
            isConnection = false;
        }
    }

    /**
     * 获取数据长度
     *
     * @param msg
     * @return
     */
    /**
     * Returns the printed width of a string in bytes (GB2312 encoding).
     * Latin characters take 1 byte and Chinese characters take 2 bytes, which
     * matches the number of character cells they use on the printer.
     *
     * @param msg the string to measure
     * @return the length in bytes
     */
    @SuppressLint("NewApi")
    private static int getBytesLength(String msg) {
        return msg.getBytes(Charset.forName("GB2312")).length;
    }


    /**
     * 打印两列
     *
     * @param leftText  左侧文字
     * @param rightText 右侧文字
     * @return
     */
    /**
     * Formats a two-column line: the left text is left-aligned, the right text is
     * right-aligned, and spaces fill the gap so the line is exactly
     * {@link #LINE_BYTE_SIZE} characters wide.
     *
     * @param leftText  text on the left
     * @param rightText text on the right
     * @return the formatted line
     */
    @SuppressLint("NewApi")
    public static String printTwoData(String leftText, String rightText) {
        StringBuilder sb = new StringBuilder();
        int leftTextLength = getBytesLength(leftText);
        int rightTextLength = getBytesLength(rightText);
        sb.append(leftText);

        // 计算两侧文字中间的空格
        int marginBetweenMiddleAndRight = LINE_BYTE_SIZE - leftTextLength - rightTextLength;

        for (int i = 0; i < marginBetweenMiddleAndRight; i++) {
            sb.append(" ");
        }
        sb.append(rightText);
        return sb.toString();
    }

    /**
     * 打印三列
     *
     * @param leftText   左侧文字
     * @param middleText 中间文字
     * @param rightText  右侧文字
     * @return
     */
    /**
     * Formats a three-column line. The middle text is centered on the middle of
     * the paper, the left text is left-aligned and the right text is right-aligned.
     *
     * @param leftText   text on the left
     * @param middleText text in the middle
     * @param rightText  text on the right
     * @return the formatted line
     */
    @SuppressLint("NewApi")
    public static String printThreeData(String leftText, String middleText, String rightText) {

        /**
         * 打印三列时，中间一列的中心线距离打印纸左侧的距离
         */
        int LEFT_LENGTH = LINE_BYTE_SIZE / 2;

        /**
         * 打印三列时，中间一列的中心线距离打印纸右侧的距离
         */
        int RIGHT_LENGTH = LINE_BYTE_SIZE / 2;

        /**
         * 打印三列时，第一列汉字最多显示几个文字
         */
        int LEFT_TEXT_MAX_LENGTH = LEFT_LENGTH / 2 - 2;

        StringBuilder sb = new StringBuilder();
        // 左边最多显示 LEFT_TEXT_MAX_LENGTH 个汉字 + 两个点
        if (leftText.length() > LEFT_TEXT_MAX_LENGTH) {
            //leftText = leftText.substring(0, LEFT_TEXT_MAX_LENGTH) + "..";
        }
        int leftTextLength = getBytesLength(leftText);
        int middleTextLength = getBytesLength(middleText);
        int rightTextLength = getBytesLength(rightText);

        sb.append(leftText);
        // 计算左侧文字和中间文字的空格长度
        int marginBetweenLeftAndMiddle = LEFT_LENGTH - leftTextLength - middleTextLength / 2;

        for (int i = 0; i < marginBetweenLeftAndMiddle; i++) {
            sb.append(" ");
        }
        sb.append(middleText);

        // 计算右侧文字和中间文字的空格长度
        int marginBetweenMiddleAndRight = RIGHT_LENGTH - middleTextLength / 2 - rightTextLength;

        for (int i = 0; i < marginBetweenMiddleAndRight; i++) {
            sb.append(" ");
        }

        // 打印的时候发现，最右边的文字总是偏右一个字符，所以需要删除一个空格
        sb.delete(sb.length() - 1, sb.length()).append(rightText);
        return sb.toString();
    }


    /**
     * 打印四列
     *
     * @param leftText   左侧文字
     * @param middleText1 中间文字
     * @param rightText  右侧文字
     * @return
     */
    /**
     * Formats a four-column line using fixed column widths. The last three
     * columns have fixed widths (6, 6 and 8 characters) and the first column
     * takes the remaining space.
     *
     * @param leftText    text in the first column
     * @param middleText1 text in the second column
     * @param middleText2 text in the third column
     * @param rightText   text in the fourth column
     * @return the formatted line
     */
    @SuppressLint("NewApi")
    public static String printFourData(String leftText, String middleText1, String middleText2, String rightText) {
        StringBuilder sb = new StringBuilder();
        /**
         * 打印三列时，中间一列的中心线距离打印纸左侧的距离
         */
        int LEFT_LENGTH = LINE_BYTE_SIZE;

        /**
         * 打印三列时，中间一列的中心线距离打印纸右侧的距离
         */
        //  int RIGHT_LENGTH_1 = LEFT_LENGTH-20;
        int RIGHT_LENGTH_2 = 6;
        int RIGHT_LENGTH_3 = 6;
        int RIGHT_LENGTH_4 = 8;
        int RIGHT_LENGTH_1 = LEFT_LENGTH - RIGHT_LENGTH_2 - RIGHT_LENGTH_3 - RIGHT_LENGTH_4;
        /**
         * 打印三列时，第一列汉字最多显示几个文字
         */

        int sub_length = 2;
        if (LINE_BYTE_SIZE == 32) {
            sub_length = 0;
        }

        int leftTextLength = getBytesLength(leftText);
        int middle1TextLength = getBytesLength(middleText1);
        int middle2TextLength = getBytesLength(middleText2);
        // int rightTextLength = getBytesLength(rightText);

        sb.append(leftText);

        for (int i = leftTextLength; i < RIGHT_LENGTH_1; i++) {
            sb.append(" ");
        }

        sb.append(middleText1);

        for (int i = RIGHT_LENGTH_1 + middle1TextLength; i < RIGHT_LENGTH_1 + RIGHT_LENGTH_2; i++) {
            sb.append(" ");
        }
        sb.append(middleText2);

        for (int i = RIGHT_LENGTH_1 + RIGHT_LENGTH_2 + middle2TextLength; i < RIGHT_LENGTH_1 + RIGHT_LENGTH_2 + RIGHT_LENGTH_3; i++) {
            sb.append(" ");
        }

        sb.append(rightText);


        // 打印的时候发现，最右边的文字总是偏右一个字符，所以需要删除一个空格
        // sb.delete(sb.length() - 3, sb.length()).append(rightText);
        return sb.toString();
    }
    /**
     * 打印四列
     *
     * @param leftText   左侧文字
     * @param middleText1 中间文字
     * @param rightText  右侧文字
     * @return
     */
    /**
     * Older four-column layout that divides the line into proportional
     * columns instead of using fixed widths.
     *
     * <p>Kept for reference; the active implementation is
     * {@link #printFourData(String, String, String, String)}.</p>
     *
     * @param leftText    text in the first column
     * @param middleText1 text in the second column
     * @param middleText2 text in the third column
     * @param rightText   text in the fourth column
     * @return the formatted line
     */
    @SuppressLint("NewApi")
    public static String printFourDataOld(String leftText, String middleText1, String middleText2, String rightText) {
        StringBuilder sb = new StringBuilder();
        /**
         * 打印三列时，中间一列的中心线距离打印纸左侧的距离
         */
        int LEFT_LENGTH = LINE_BYTE_SIZE / 2;

        /**
         * 打印三列时，中间一列的中心线距离打印纸右侧的距离
         */
        int RIGHT_LENGTH = LINE_BYTE_SIZE / 2;

        /**
         * 打印三列时，第一列汉字最多显示几个文字
         */

        int sub_length = 2;
        if (LINE_BYTE_SIZE == 32) {
            sub_length = 0;
        }

        int sub_length2 = 1;
        // if(LINE_BYTE_SIZE==32){
        //  sub_length2=1;
        //  }

        int LEFT_TEXT_MAX_LENGTH = LEFT_LENGTH / 2 - sub_length;

        // 左边最多显示 LEFT_TEXT_MAX_LENGTH 个汉字 + 两个点
        if (leftText.length() > (LEFT_TEXT_MAX_LENGTH + 2) / 2) {
            //leftText = leftText.substring(0, (LEFT_TEXT_MAX_LENGTH+2)/2-1) + ".";
        }
        int leftTextLength = getBytesLength(leftText);
        int middle1TextLength = getBytesLength(middleText1);
        int middle2TextLength = getBytesLength(middleText2);
        int rightTextLength = getBytesLength(rightText);

        sb.append(leftText);
        // 计算左侧文字和中间文字的空格长度
        int marginBetweenLeftAndMiddle1 = LEFT_LENGTH - leftTextLength - middle1TextLength;

        for (int i = LEFT_LENGTH / 4 - sub_length2; i < marginBetweenLeftAndMiddle1; i++) {
            sb.append(" ");
        }
        sb.append(middleText1);


        // 计算右侧文字和中间文字的空格长度
        int marginBetweenMiddleAndRight = RIGHT_LENGTH - middle2TextLength - rightTextLength;

        for (int i = RIGHT_LENGTH / 4 - sub_length2; i < marginBetweenMiddleAndRight; i++) {
            sb.append(" ");
        }
        sb.append(middleText2);

        // 计算右侧文字和中间文字的空格长度
        int marginBetweenMiddle2AndRight = RIGHT_LENGTH - middle2TextLength - rightTextLength;

        for (int i = RIGHT_LENGTH / 4 - sub_length2; i < marginBetweenMiddle2AndRight; i++) {
            sb.append(" ");
        }
        // 打印的时候发现，最右边的文字总是偏右一个字符，所以需要删除一个空格
        sb.delete(sb.length() - 3, sb.length()).append(rightText);
        return sb.toString();
    }


    /**
     * 向StringBuilder中添加指定数量的相同字符
     *
     * @param printCount   添加的字符数量
     * @param identicalStr 添加的字符
     */
    /**
     * Appends the same string to a {@link StringBuilder} several times.
     *
     * @param builder      the builder to append to
     * @param printCount   number of repetitions
     * @param identicalStr the string to repeat
     */
    private static void addIdenticalStrToStringBuilder(StringBuilder builder, int printCount, String identicalStr) {
        for (int i = 0; i < printCount; i++) {
            builder.append(identicalStr);
        }
    }

    /**
     * 根据字符串截取前指定字节数,按照GBK编码进行截取
     *
     * @param str 原字符串
     * @param len 截取的字节数
     * @return 截取后的字符串
     */
    /**
     * Returns the first {@code len} bytes of a string using GBK encoding, without
     * cutting a double-byte character in half.
     *
     * @param str the source string
     * @param len maximum number of bytes
     * @return the truncated string, the original string if it already fits, or
     * {@code null} if nothing fits or an error occurs
     */
    private static String subStringByGBK(String str, int len) {
        String result = null;
        if (str != null) {
            try {
                byte[] a = str.getBytes("GBK");
                if (a.length <= len) {
                    result = str;
                } else if (len > 0) {
                    result = new String(a, 0, len, "GBK");
                    int length = result.length();
                    if (str.charAt(length - 1) != result.charAt(length - 1)) {
                        if (length < 2) {
                            result = null;
                        } else {
                            result = result.substring(0, length - 1);
                        }
                    }
                }
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
        return result;
    }

    /**
     * 添加换行符
     */
    /**
     * Appends a line break to a {@link StringBuilder}.
     *
     * @param builder the builder to append to
     */
    private static void addLineSeparator(StringBuilder builder) {
        builder.append("\n");
    }

    /**
     * 在GBK编码下，获取其字符串占据的字符个数
     */
    /**
     * Returns the number of character cells a string uses when encoded as GBK
     * (1 byte per Latin character, 2 bytes per Chinese character).
     *
     * @param text the string to measure
     * @return the length in bytes, or 0 if encoding fails
     */
    private static int getCharCountByGBKEncoding(String text) {
        try {
            return text.getBytes("GBK").length;
        } catch (Exception e) {
            e.printStackTrace();
            return 0;
        }
    }


    /**
     * 打印相关配置
     */
    /**
     * Print options.
     */
    public static class PrintConfig {
        public int maxLength = 30;

        public boolean printBarcode = false;  // 打印条码
        public boolean printQrCode = false;   // 打印二维码
        public boolean printEndText = true;   // 打印结束语
        public boolean needCutPaper = false;  // 是否切纸
    }


    /**
     * 打印二维码
     * @param qrCode
     * @return
     */
    /**
     * Builds the ESC/POS command sequence that prints a QR code
     * ({@code GS ( k} commands): select model 2, set module size 8, set error
     * correction level to 15% (L = 0x31), store the data and print the symbol.
     *
     * @param qrCode the content to encode
     * @return the command bytes to send to the printer
     */
    public static byte[] getQrCodeCmd(String qrCode) {
        byte[] data;
        int store_len = qrCode.length() + 3;
        byte store_pL = (byte) (store_len % 256);
        byte store_pH = (byte) (store_len / 256);

        // QR Code: Select the model
        //              Hex     1D      28      6B      04      00      31      41      n1(x32)     n2(x00) - size of model
        // set n1 [49 x31, model 1] [50 x32, model 2] [51 x33, micro qr code]
        // https://download4.epson.biz/sec_pubs/pos/reference_en/escpos/gs_lparen_lk_fn165.html
        byte[] modelQR = {(byte) 0x1d, (byte) 0x28, (byte) 0x6b, (byte) 0x04, (byte) 0x00, (byte) 0x31, (byte) 0x41, (byte) 0x32, (byte) 0x00};

        // QR Code: Set the size of module
        // Hex      1D      28      6B      03      00      31      43      n
        // n depends on the printer
        // https://download4.epson.biz/sec_pubs/pos/reference_en/escpos/gs_lparen_lk_fn167.html
        byte[] sizeQR = {(byte) 0x1d, (byte) 0x28, (byte) 0x6b, (byte) 0x03, (byte) 0x00, (byte) 0x31, (byte) 0x43, (byte) 0x08};

        // QR Code: Select the error correction level
        //          Hex     1D      28      6B      03      00      31      45      n
        // Set n for error correction [48 x30 -> 7%] [49 x31-> 15%] [50 x32 -> 25%] [51 x33 -> 30%]
        // https://download4.epson.biz/sec_pubs/pos/reference_en/escpos/gs_lparen_lk_fn169.html
        byte[] errorQR = {(byte) 0x1d, (byte) 0x28, (byte) 0x6b, (byte) 0x03, (byte) 0x00, (byte) 0x31, (byte) 0x45, (byte) 0x31};

        // QR Code: Store the data in the symbol storage area
        // Hex      1D      28      6B      pL      pH      31      50      30      d1...dk
        // https://download4.epson.biz/sec_pubs/pos/reference_en/escpos/gs_lparen_lk_fn180.html
        //                        1D          28          6B         pL          pH  cn(49->x31) fn(80->x50) m(48->x30) d1…dk
        byte[] storeQR = {(byte) 0x1d, (byte) 0x28, (byte) 0x6b, store_pL, store_pH, (byte) 0x31, (byte) 0x50, (byte) 0x30};

        // QR Code: Print the symbol data in the symbol storage area
        // Hex      1D      28      6B      03      00      31      51      m
        // https://download4.epson.biz/sec_pubs/pos/reference_en/escpos/gs_lparen_lk_fn181.html
        byte[] printQR = {(byte) 0x1d, (byte) 0x28, (byte) 0x6b, (byte) 0x03, (byte) 0x00, (byte) 0x31, (byte) 0x51, (byte) 0x30};

        data = byteMerger(modelQR, sizeQR);
        data = byteMerger(data, errorQR);
        data = byteMerger(data, storeQR);
        data = byteMerger(data, qrCode.getBytes());
        data = byteMerger(data, printQR);

        return data;
    }

    /**
     * 打印条码
     * @param barcode
     * @return
     */
    /**
     * Builds the ESC/POS command sequence that prints a Code-128 barcode.
     *
     * <p>Code-128 needs a character set prefix: {@code "{A"} for upper-case
     * letters, {@code "{B"} for all letters, digits and symbols, and
     * {@code "{C"} for digit pairs (00-99). Short codes use set B directly; for
     * long codes (18+ characters) runs of 10 or more digits are packed using
     * set C to make the barcode shorter.</p>
     *
     * <p>The barcode is printed with the human-readable text below it, module
     * width 2 and height 254 (0xFE).</p>
     *
     * @param barcode the barcode content
     * @return the command bytes as a string, ready for {@link #printText(String)}
     */
    public static String getBarcodeCmd(String barcode) {
        // 打印 Code-128 条码时需要使用字符集前缀
        // "{A" 表示大写字母
        // "{B" 表示所有字母，数字，符号
        // "{C" 表示数字，可以表示 00 - 99 的范围


        byte[] data;

        String btEncode;

        if (barcode.length() < 18) {
            // 字符长度小于15的时候直接输出字符串
            btEncode = "{B" + barcode;
        } else {
            // 否则做一点优化

            int startPos = 0;
            btEncode = "{B";

            for (int i = 0; i < barcode.length(); i++) {
                char curChar = barcode.charAt(i);

                if (curChar < 48 || curChar > 57 || i == (barcode.length() - 1)) {
                    // 如果是非数字或者是最后一个字符

                    if (i - startPos >= 10) {
                        if (startPos == 0) {
                            btEncode = "";
                        }

                        btEncode += "{C";

                        boolean isFirst = true;
                        int numCode = 0;

                        for (int j = startPos; j < i; j++) {

                            if (isFirst) { // 处理第一位
                                numCode = (barcode.charAt(j) - 48) * 10;
                                isFirst = false;
                            } else { // 处理第二位
                                numCode += (barcode.charAt(j) - 48);
                                btEncode += (char) numCode;
                                isFirst = true;
                            }

                        }

                        btEncode += "{B";

                        if (!isFirst) {
                            startPos = i - 1;
                        } else {
                            startPos = i;
                        }
                    }

                    for (int k = startPos; k <= i; k++) {
                        btEncode += barcode.charAt(k);
                    }
                    startPos = i + 1;
                }

            }
        }


        // 设置 HRI 的位置，02 表示下方
        byte[] hriPosition = {(byte) 0x1d, (byte) 0x48, (byte) 0x02};
        // 最后一个参数表示宽度 取值范围 1-6 如果条码超长则无法打印
        byte[] width = {(byte) 0x1d, (byte) 0x77, (byte) 0x02};
        byte[] height = {(byte) 0x1d, (byte) 0x68, (byte) 0xfe};
        // 最后两个参数 73 ： CODE 128 || 编码的长度
        byte[] barcodeType = {(byte) 0x1d, (byte) 0x6b, (byte) 73, (byte) btEncode.length()};
        byte[] print = {(byte) 10, (byte) 0};

        data = byteMerger(hriPosition, width);
        data = byteMerger(data, height);
        data = byteMerger(data, barcodeType);
        data = byteMerger(data, btEncode.getBytes());
        data = byteMerger(data, print);

        return new String(data);
    }

    /**
     * 切纸
     * @return
     */
    /**
     * Returns the command that feeds the paper and cuts it
     * ({@code GS V 66 n}). The last byte (0x15) controls how far the paper is
     * fed before cutting.
     *
     * @return the cut command bytes
     */
    public static byte[] getCutPaperCmd() {
        // 走纸并切纸，最后一个参数控制走纸的长度
        byte[] data = {(byte) 0x1d, (byte) 0x56, (byte) 0x42, (byte) 0x15};

        return data;
    }

    /**
     * 对齐方式
     * @param alignMode
     * @return
     */
    /**
     * Returns the alignment command for the given alignment value.
     *
     * @param alignMode {@link #ALIGN_LEFT_NEW}, {@link #ALIGN_CENTER_NEW} or {@link #ALIGN_RIGHT_NEW}
     * @return the {@code ESC a n} command bytes (left alignment for unknown values)
     */
    public static byte[] getAlignCmd(int alignMode) {
        byte[] data = {(byte) 0x1b, (byte) 0x61, (byte) 0x0};
        if (alignMode == ALIGN_LEFT_NEW) {
            data[2] = (byte) 0x00;
        } else if (alignMode == ALIGN_CENTER_NEW) {
            data[2] = (byte) 0x01;
        } else if (alignMode == ALIGN_RIGHT_NEW) {
            data[2] = (byte) 0x02;
        }

        return data;
    }

    /**
     * 字体大小
     * @param fontSize
     * @return
     */
    /**
     * Returns the character size command ({@code GS ! n}) for the given font
     * size value. In {@code n}, the high nibble is the width multiplier minus 1
     * and the low nibble is the height multiplier minus 1.
     *
     * @param fontSize one of the {@code FONT_*_NEW} constants
     * @return the command bytes (normal size for unknown values)
     */
    public static byte[] getFontSizeCmd(int fontSize) {
        byte[] data = {(byte) 0x1d, (byte) 0x21, (byte) 0x0};
        if (fontSize == FONT_NORMAL_NEW) {
            data[2] = (byte) 0x00;
        } else if (fontSize == FONT_MIDDLE_NEW) {
            data[2] = (byte) 0x01;
        } else if (fontSize == FONT_BIG_NEW) {
            data[2] = (byte) 0x11;
        } else if (fontSize == FONT_BIG_NEW3) {
            data[2] = (byte) 0x10;
        } else if (fontSize == FONT_BIG_NEW4) {
            data[2] = (byte) 0x12;
        } else if (fontSize == FONT_BIG_NEW5) {
            data[2] = (byte) 0x21;
        } else if (fontSize == FONT_BIG_NEW6) {
            data[2] = (byte) 0x22;
        } else if (fontSize == FONT_BIG_NEW7) {
            data[2] = (byte) 0x33;
        } else if (fontSize == FONT_BIG_NEW8) {
            data[2] = (byte) 0x44;
        }

        return data;
    }

    /**
     * 加粗模式
     * @param fontBold
     * @return
     */
    /**
     * Returns the bold mode command ({@code ESC E n}).
     *
     * @param fontBold {@link #FONT_BOLD_NEW} turns bold on,
     *                 {@link #FONT_BOLD_CANCEL_NEW} turns it off
     * @return the command bytes
     */
    public static byte[] getFontBoldCmd(int fontBold) {
        byte[] data = {(byte) 0x1b, (byte) 0x45, (byte) 0x0};

        if (fontBold == FONT_BOLD_NEW) {
            data[2] = (byte) 0x01;
        } else if (fontBold == FONT_BOLD_CANCEL_NEW) {
            data[2] = (byte) 0x00;
        }

        return data;
    }

    /**
     * 打开钱箱
     * @return
     */
    /**
     * Returns the command that opens the cash drawer ({@code DLE DC4}).
     *
     * @return the command bytes as a string
     */
    public static String getOpenDrawerCmd() {
        byte[] data = new byte[4];
        data[0] = 0x10;
        data[1] = 0x14;
        data[2] = 0x00;
        data[3] = 0x00;

        return new String(data);
    }

    /**
     * 字符串转字节数组
     * @param str
     * @return
     */
    /**
     * Converts a string to GBK-encoded bytes (going through UTF-8 first).
     *
     * @param str the source string
     * @return the GBK bytes, or {@code null} if the encoding is unsupported
     */
    public static byte[] stringToBytes(String str) {
        byte[] data = null;

        try {
            byte[] strBytes = str.getBytes("utf-8");

            data = (new String(strBytes, "utf-8")).getBytes("gbk");
        } catch (UnsupportedEncodingException exception) {
            exception.printStackTrace();
        }

        return data;
    }

    /**
     * 字节数组合并
     * @param bytesA
     * @param bytesB
     * @return
     */
    /**
     * Concatenates two byte arrays.
     *
     * @param bytesA first array
     * @param bytesB second array
     * @return a new array containing {@code bytesA} followed by {@code bytesB}
     */
    public static byte[] byteMerger(byte[] bytesA, byte[] bytesB) {
        byte[] bytes = new byte[bytesA.length + bytesB.length];
        System.arraycopy(bytesA, 0, bytes, 0, bytesA.length);
        System.arraycopy(bytesB, 0, bytes, bytesA.length, bytesB.length);
        return bytes;
    }

    /**
     * Called by Cordova when the plugin is destroyed.
     */
    @Override
    public void onDestroy() {
        super.onDestroy();
        closeQuietly();

    }
}
