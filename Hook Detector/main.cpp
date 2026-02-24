#include "imgui.h"
#include "imgui_impl_win32.h"
#include "imgui_impl_dx11.h"
#include <d3d11.h>
#include <tchar.h>
#include <vector>
#include <string>
#include <tlhelp32.h>
#include "winternl.h"
#include <format>
#include "securitybaseapi.h"
#pragma comment(lib, "d3d11.lib")


// DirectX globals
static ID3D11Device* g_pd3dDevice = nullptr;
static ID3D11DeviceContext* g_pd3dDeviceContext = nullptr;
static IDXGISwapChain* g_pSwapChain = nullptr;
static ID3D11RenderTargetView* g_mainRenderTargetView = nullptr;

// Forward declarations
bool CreateDeviceD3D(HWND hWnd);
void CleanupDeviceD3D();
void CreateRenderTarget();
void CleanupRenderTarget();
LRESULT WINAPI WndProc(HWND hWnd, UINT msg, WPARAM wParam, LPARAM lParam);
extern IMGUI_IMPL_API LRESULT ImGui_ImplWin32_WndProcHandler(HWND hWnd, UINT msg, WPARAM wParam, LPARAM lParam);




typedef __kernel_entry NTSTATUS NtQueryInformationProcess_t(
                HANDLE           ProcessHandle,
                int              ProcessInformationClass,
                PVOID            ProcessInformation,
                ULONG            ProcessInformationLength,
                PULONG           ReturnLength
);


NtQueryInformationProcess_t* fNtQueryInformationProcess = nullptr;


enum class Severity {
    Info,
    Warning,
    Detection,
    Critical
};

ImVec4 GetSeverityColor(Severity s) {
    switch (s) {
    case Severity::Info:      return { 0.4f, 1.0f, 0.4f, 1.0f };   // green
    case Severity::Warning:   return { 1.0f, 0.8f, 0.2f, 1.0f };   // yellow
    case Severity::Detection: return { 1.0f, 0.4f, 0.4f, 1.0f };   // red
    case Severity::Critical:  return { 1.0f, 0.2f, 0.8f, 1.0f };   // magenta
    default:                  return { 1.0f, 1.0f, 1.0f, 1.0f };
    }
}

struct ScanResult {
    std::string description;
    Severity severity;
};


struct ProcessInfo {
    DWORD pid;
    wchar_t name[MAX_PATH];
};

static std::vector<ProcessInfo> g_processes;
static std::vector<ScanResult> g_results;
static int g_selectedPid = 0;
static bool g_scanning = false;


void RefreshProcessList() {
    g_processes.clear();
    HANDLE snap = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
    if (snap == INVALID_HANDLE_VALUE) return;

    PROCESSENTRY32 pe = { sizeof(pe) };
    if (Process32First(snap, &pe)) {
        do {
            ProcessInfo info;
            info.pid = pe.th32ProcessID;
            wcscpy_s(info.name, pe.szExeFile);
            g_processes.push_back(info);
        } while (Process32Next(snap, &pe));
    }
    CloseHandle(snap);
}

DWORD rvaToOffset(BYTE* fileBuffer, DWORD rva) {
    auto dos = (IMAGE_DOS_HEADER*)fileBuffer;
    auto ntHeaders = (IMAGE_NT_HEADERS*)(fileBuffer + dos->e_lfanew);
    auto section = IMAGE_FIRST_SECTION(ntHeaders);

    for (int i = 0; i < ntHeaders->FileHeader.NumberOfSections; i++) {
        if (rva >= section[i].VirtualAddress &&
            rva < section[i].VirtualAddress + section[i].Misc.VirtualSize) {
            return rva - section[i].VirtualAddress + section[i].PointerToRawData;
        }
    }
    return 0;
}

bool isInTextSection(BYTE* fileBuffer, DWORD rva) {
    auto dos = (IMAGE_DOS_HEADER*)fileBuffer;
    auto nt = (IMAGE_NT_HEADERS*)(fileBuffer + dos->e_lfanew);
    auto section = IMAGE_FIRST_SECTION(nt);

    for (int i = 0; i < nt->FileHeader.NumberOfSections; i++) {
        if (strcmp((char*)section[i].Name, ".text") == 0) {
            return rva >= section[i].VirtualAddress &&
                rva < section[i].VirtualAddress + section[i].Misc.VirtualSize;
        }
    }
    return false;
}

void enableDebugPrivilige() {
    HANDLE token;
    OpenProcessToken(GetCurrentProcess(), TOKEN_ADJUST_PRIVILEGES, &token);

    TOKEN_PRIVILEGES tp;
    LookupPrivilegeValue(NULL, SE_DEBUG_NAME, &tp.Privileges[0].Luid);
    tp.PrivilegeCount = 1;
    tp.Privileges[0].Attributes = SE_PRIVILEGE_ENABLED;

    AdjustTokenPrivileges(token, FALSE, &tp, 0, NULL, NULL);
    CloseHandle(token);

}

uintptr_t resolveHookTarget(uint8_t* hookedBytes, uintptr_t address, HANDLE handle, int depth = 0) {
    if (depth >= 5) return 0;


    uintptr_t target = 0;

    // mov r64, imm64
    if ((hookedBytes[0] == 0x48 || hookedBytes[0] == 0x49) &&
        (hookedBytes[1] >= 0xB8 && hookedBytes[1] <= 0xBF)) {
       target = *reinterpret_cast<uintptr_t*>(hookedBytes + 2);
    }

    // jmp, xxxxx
    else if (hookedBytes[0] == 0xE9) {
        int32_t rel = *reinterpret_cast<int32_t*>(hookedBytes + 1);
        target = address + 5 + rel;

    }
    //jmp to pointer, so we need to deref it to get real address
    else if (hookedBytes[0] == 0xFF && hookedBytes[1] == 0x25) {
        int32_t rel = *reinterpret_cast<int32_t*>(hookedBytes + 2);
        uintptr_t ptrAddr = address + 6 + rel;
        ReadProcessMemory(handle, (LPCVOID)ptrAddr, &target, sizeof(target), nullptr);
    }

    if (target == 0) return 0;


    // follow jump chains recursively (e.g. E9 -> FF 25 -> final destination)
    BYTE nextBytes[16] = { 0 };
    if (ReadProcessMemory(handle, (LPCVOID)target, nextBytes, sizeof(nextBytes), nullptr)) {
        if (nextBytes[0] == 0xE9 || nextBytes[0] == 0xFF ||
            ((nextBytes[0] == 0x48 || nextBytes[0] == 0x49) && nextBytes[1] >= 0xB8 && nextBytes[1] <= 0xBF)) {
            return resolveHookTarget(nextBytes, target, handle, depth + 1);
        }
    }
    return target;
}

std::string resolveAddressToModule(uintptr_t address, int pid) {
    auto handle = OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, FALSE, pid);

    if (!handle) {
        auto error = GetLastError();
        auto buf = std::format("[!] Failed to open handle to process: {}", error);
        g_results.push_back({ buf, Severity::Critical });
        return "";
    }

    PROCESS_BASIC_INFORMATION pbi;
    ULONG returnLength;
    fNtQueryInformationProcess(handle, 0, &pbi, sizeof(pbi), &returnLength);

    PEB peb;
    ReadProcessMemory(handle, pbi.PebBaseAddress, &peb, sizeof(peb), nullptr);

    PEB_LDR_DATA ldr;
    ReadProcessMemory(handle, peb.Ldr, &ldr, sizeof(ldr), nullptr);

    LIST_ENTRY* head = (LIST_ENTRY*)((uintptr_t)peb.Ldr + offsetof(PEB_LDR_DATA, InMemoryOrderModuleList));
    LIST_ENTRY* current = ldr.InMemoryOrderModuleList.Flink;

   // ReadProcessMemory(handle, current, &current, sizeof(current), nullptr);


    while (current != head) {
        LDR_DATA_TABLE_ENTRY entry;
        ReadProcessMemory(handle, (BYTE*)current - 0x10, &entry, sizeof(entry), nullptr);
        
        IMAGE_DOS_HEADER dos;
        ReadProcessMemory(handle, entry.DllBase, &dos, sizeof(dos), nullptr);
        IMAGE_NT_HEADERS ntHeaders;
        ReadProcessMemory(handle, (BYTE*)entry.DllBase + dos.e_lfanew, &ntHeaders, sizeof(ntHeaders), nullptr);

        auto base = (uintptr_t)entry.DllBase;
        auto size = ntHeaders.OptionalHeader.SizeOfImage;

        if (address >= base && address < base + size) {
            wchar_t fullDllName[MAX_PATH];
            ReadProcessMemory(handle, entry.FullDllName.Buffer, &fullDllName, entry.FullDllName.Length, nullptr);
            fullDllName[entry.FullDllName.Length / sizeof(wchar_t)] = L'\0';

            auto basename = wcsrchr(fullDllName, L'\\');
            if (basename) basename++; // skip the double backslash
            else basename = fullDllName;





            std::wstring wDllName(basename);
            std::string sDllName(wDllName.begin(), wDllName.end());

            auto offset = address - base;

            CloseHandle(handle);

            return std::format("{}-0x{:X}", sDllName.c_str(), offset);
        }
        current = entry.InMemoryOrderLinks.Flink;
    }
    CloseHandle(handle);
    return std::format("Unkown region-{:X}", address);
}

const wchar_t* targetModules[] = {
    L"ntdll.dll",
    L"kernel32.dll",
    L"kernelbase.dll",
    L"user32.dll",
    L"win32u.dll"
};


void RunScan(int pid) {
    g_results.clear();
    g_scanning = true;



    auto handle = OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, FALSE, pid);
    
    if (!handle) {
        auto error = GetLastError();
        auto buf = std::format("[!] Failed to open handle to process: {}", error);
        g_results.push_back({ buf, Severity::Critical});
        return;
    }

    PROCESS_BASIC_INFORMATION pbi;
    ULONG returnLength;
    fNtQueryInformationProcess(handle, 0, &pbi, sizeof(pbi), &returnLength);

    PEB peb;
    ReadProcessMemory(handle, pbi.PebBaseAddress, &peb, sizeof(peb), nullptr);

    PEB_LDR_DATA ldr;
    ReadProcessMemory(handle, peb.Ldr, &ldr, sizeof(ldr), nullptr);

    LIST_ENTRY* head = (LIST_ENTRY*)((uintptr_t)peb.Ldr + offsetof(PEB_LDR_DATA, InMemoryOrderModuleList));
    LIST_ENTRY* current = ldr.InMemoryOrderModuleList.Flink;

    ReadProcessMemory(handle, current, &current, sizeof(current), nullptr);


    while (current != head) {
        LDR_DATA_TABLE_ENTRY entry;
        ReadProcessMemory(handle, (BYTE*)current - 0x10, &entry, sizeof(entry), nullptr);

        wchar_t dllName[MAX_PATH];
        ReadProcessMemory(handle, entry.FullDllName.Buffer, dllName, entry.FullDllName.Length, nullptr);
        dllName[entry.FullDllName.Length / sizeof(wchar_t)] = L'\0';

        wchar_t* baseName = wcsrchr(dllName, L'\\');
        if (baseName) baseName++;
        else baseName = dllName;

        //bool isTarget = false;
        //for (auto& mod : targetModules) {
        //    if (_wcsicmp(baseName, mod) == 0) {
        //        isTarget = true;
        //        break;
        //    }
        //}
        //if (!isTarget) {
        //    current = entry.InMemoryOrderLinks.Flink;
        //    continue;
        //}



        IMAGE_DOS_HEADER dos;
        ReadProcessMemory(handle, entry.DllBase, &dos, sizeof(dos), nullptr);
        IMAGE_NT_HEADERS ntHeaders;
        ReadProcessMemory(handle, (BYTE*)entry.DllBase + dos.e_lfanew, &ntHeaders, sizeof(ntHeaders), nullptr);

        IMAGE_EXPORT_DIRECTORY exportDir;
        ReadProcessMemory(handle, (BYTE*)entry.DllBase + ntHeaders.OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXPORT].VirtualAddress, &exportDir, sizeof(exportDir), nullptr);

        auto exportDirRVA = ntHeaders.OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXPORT].VirtualAddress;
        auto exportDirSize = ntHeaders.OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXPORT].Size;

        auto addressOfNames = new DWORD[exportDir.NumberOfNames];
        ReadProcessMemory(handle, (BYTE*)entry.DllBase + exportDir.AddressOfNames, addressOfNames, exportDir.NumberOfNames * sizeof(DWORD), nullptr);

        auto addressOfFunctions = new DWORD[exportDir.NumberOfFunctions];
        ReadProcessMemory(handle, (BYTE*)entry.DllBase + exportDir.AddressOfFunctions, addressOfFunctions, exportDir.NumberOfFunctions * sizeof(DWORD), nullptr);

        auto addressOfOrdinals = new WORD[exportDir.NumberOfNames];
        ReadProcessMemory(handle, (BYTE*)entry.DllBase + exportDir.AddressOfNameOrdinals, addressOfOrdinals, exportDir.NumberOfNames * sizeof(WORD), nullptr);

        HANDLE hFile = CreateFileW(dllName, GENERIC_READ, FILE_SHARE_READ, nullptr, OPEN_EXISTING, 0, nullptr);
        HANDLE hMapping = CreateFileMappingW(hFile, nullptr, PAGE_READONLY | SEC_IMAGE, 0, 0, nullptr);
        auto mappedFile = (BYTE*)MapViewOfFile(hMapping, FILE_MAP_READ, 0, 0, 0);
        CloseHandle(hFile);

        char dllNameC[MAX_PATH];
        size_t converted;
        wcstombs_s(&converted, dllNameC, baseName, _TRUNCATE);

        char modBuf[512];
        sprintf_s(modBuf, sizeof(modBuf), "[+] Scanning: %s (%d exports)", dllNameC, exportDir.NumberOfNames);
        g_results.push_back({ modBuf, Severity::Info });

        for (DWORD i = 0; i < exportDir.NumberOfNames; i++) {
            DWORD funcRVA = addressOfFunctions[addressOfOrdinals[i]];

            if (funcRVA == 0) continue;
            if (funcRVA >= exportDirRVA && funcRVA < exportDirRVA + exportDirSize) continue;
            if (!isInTextSection(mappedFile, funcRVA)) continue;

            BYTE remoteBytes[16] = { 0 };
            ReadProcessMemory(handle, (BYTE*)entry.DllBase + funcRVA, remoteBytes, sizeof(remoteBytes), nullptr);

            auto cleanBytes = mappedFile + funcRVA;

            if (memcmp(remoteBytes, cleanBytes, 16) != 0) {
                char funcName[256];
                ReadProcessMemory(handle, (BYTE*)entry.DllBase + addressOfNames[i], funcName, sizeof(funcName), nullptr);

                char cleanHex[128], remoteHex[128];
                int co = 0, ro = 0;
                for (int j = 0; j < 16; j++) {
                    co += sprintf_s(cleanHex + co, sizeof(cleanHex) - co, "%02X ", cleanBytes[j]);
                    ro += sprintf_s(remoteHex + ro, sizeof(remoteHex) - ro, "%02X ", remoteBytes[j]);
                }

                auto funcAddress = (uintptr_t)entry.DllBase + funcRVA;
                auto targetAddress = resolveHookTarget(remoteBytes, funcAddress, handle);
                auto moduleNameAndOffset = resolveAddressToModule(targetAddress, pid);

                auto buf = std::format("[!] Hook detected : {}!{}\n    Clean : {}\n    Hooked: {}\n    Resolves to: {}", dllNameC, funcName, cleanHex, remoteHex, moduleNameAndOffset.c_str());

                /*char buf[512];
                sprintf_s(buf, sizeof(buf), "[!] Hook detected: %s!%s\n    Clean:  %s\n    Hooked: %s", dllNameC, funcName, cleanHex, remoteHex);*/
                g_results.push_back({ buf.c_str(), Severity::Detection});
            }
        }

        UnmapViewOfFile(mappedFile);
        CloseHandle(hMapping);
        delete[] addressOfNames;
        delete[] addressOfFunctions;
        delete[] addressOfOrdinals;

        current = entry.InMemoryOrderLinks.Flink;
    }

    if (g_results.size() == 0) {
        g_results.push_back({ "[+] No hooks detected.", Severity::Info });
    }

    CloseHandle(handle);   
    g_scanning = false;
}

// ============================================================
// IMGUI RENDER
// ============================================================

void RenderUI() {
    // Main window fills the viewport
    ImGui::SetNextWindowPos(ImVec2(0, 0));
    ImGui::SetNextWindowSize(ImGui::GetIO().DisplaySize);
    ImGui::Begin("Scanner", nullptr,
        ImGuiWindowFlags_NoResize |
        ImGuiWindowFlags_NoMove |
        ImGuiWindowFlags_NoCollapse |
        ImGuiWindowFlags_NoTitleBar);

    // Header
    ImGui::TextColored(ImVec4(0.4f, 0.8f, 1.0f, 1.0f), "Hook Detector");
    ImGui::Separator();
    ImGui::Spacing();

    // Process selection
    static int selectedIndex = -1;
    static char preview[512] = "Select process...";

    if (ImGui::Button("Refresh")) {
        RefreshProcessList();
    }
    ImGui::SameLine();

    ImGui::SetNextItemWidth(300);
    if (ImGui::BeginCombo("##process", preview)) {
        for (int i = 0; i < g_processes.size(); i++) {
            char nameA[MAX_PATH];
            size_t converted;
            wcstombs_s(&converted, nameA, g_processes[i].name, _TRUNCATE);

            char label[512];
            sprintf_s(label, sizeof(label), "[%d] %s", g_processes[i].pid, nameA);

            if (ImGui::Selectable(label, selectedIndex == i)) {
                selectedIndex = i;
                g_selectedPid = g_processes[i].pid;
                sprintf_s(preview, sizeof(preview), "[%d] %s", g_processes[i].pid, nameA);
            }
        }
        ImGui::EndCombo();
    }

    ImGui::SameLine();
    if (ImGui::Button("Scan", ImVec2(100, 0))) {
        RunScan(g_selectedPid);
    }
    ImGui::SameLine();
    if (ImGui::Button("Clear", ImVec2(100, 0))) {
        g_results.clear();
    }

    ImGui::Spacing();
    ImGui::Separator();
    ImGui::Spacing();

    // Results panel
    ImGui::Text("Results (%d)", (int)g_results.size());
    ImGui::BeginChild("Results", ImVec2(0, 0), true);

    for (auto& result : g_results) {
        ImGui::TextColored(GetSeverityColor(result.severity), "%s", result.description.c_str());
    }

    ImGui::EndChild();
    ImGui::End();
}

// ============================================================
// WINMAIN + D3D BOILERPLATE
// ============================================================

int WINAPI WinMain(HINSTANCE hInstance, HINSTANCE, LPSTR, int) {


    fNtQueryInformationProcess = (NtQueryInformationProcess_t*)GetProcAddress(GetModuleHandleA("ntdll.dll"), "NtQueryInformationProcess");

    enableDebugPrivilige();


    WNDCLASSEXW wc = {
        sizeof(wc), CS_CLASSDC, WndProc, 0L, 0L,
        GetModuleHandle(nullptr), nullptr, nullptr, nullptr, nullptr,
        L"ScannerClass", nullptr
    };
    RegisterClassExW(&wc);

    HWND hwnd = CreateWindowW(
        wc.lpszClassName, L"Scanner",
        WS_OVERLAPPEDWINDOW,
        100, 100, 800, 500,
        nullptr, nullptr, wc.hInstance, nullptr
    );

    if (!CreateDeviceD3D(hwnd)) {
        CleanupDeviceD3D();
        UnregisterClassW(wc.lpszClassName, wc.hInstance);
        return 1;
    }

    ShowWindow(hwnd, SW_SHOWDEFAULT);
    UpdateWindow(hwnd);

    // Setup ImGui
    IMGUI_CHECKVERSION();
    ImGui::CreateContext();
    ImGuiIO& io = ImGui::GetIO();
    io.ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard;

    // Dark theme with custom accent
    ImGui::StyleColorsDark();
    ImGuiStyle& style = ImGui::GetStyle();
    style.WindowRounding = 0.0f;
    style.FrameRounding = 4.0f;
    style.GrabRounding = 4.0f;
    style.WindowBorderSize = 0.0f;
    style.FramePadding = ImVec2(8, 4);
    style.ItemSpacing = ImVec2(8, 6);

    // Accent colors
    style.Colors[ImGuiCol_Button] = ImVec4(0.20f, 0.40f, 0.65f, 1.00f);
    style.Colors[ImGuiCol_ButtonHovered] = ImVec4(0.28f, 0.50f, 0.75f, 1.00f);
    style.Colors[ImGuiCol_ButtonActive] = ImVec4(0.15f, 0.35f, 0.60f, 1.00f);
    style.Colors[ImGuiCol_FrameBg] = ImVec4(0.12f, 0.12f, 0.15f, 1.00f);
    style.Colors[ImGuiCol_WindowBg] = ImVec4(0.08f, 0.08f, 0.10f, 1.00f);
    style.Colors[ImGuiCol_ChildBg] = ImVec4(0.10f, 0.10f, 0.12f, 1.00f);

    ImGui_ImplWin32_Init(hwnd);
    ImGui_ImplDX11_Init(g_pd3dDevice, g_pd3dDeviceContext);

    // Main loop
    MSG msg;
    ZeroMemory(&msg, sizeof(msg));

    RefreshProcessList();

    while (msg.message != WM_QUIT) {
        if (PeekMessage(&msg, nullptr, 0U, 0U, PM_REMOVE)) {
            TranslateMessage(&msg);
            DispatchMessage(&msg);
            continue;
        }

        ImGui_ImplDX11_NewFrame();
        ImGui_ImplWin32_NewFrame();
        ImGui::NewFrame();

        RenderUI();

        ImGui::Render();
        const float clear_color[4] = { 0.06f, 0.06f, 0.08f, 1.00f };
        g_pd3dDeviceContext->OMSetRenderTargets(1, &g_mainRenderTargetView, nullptr);
        g_pd3dDeviceContext->ClearRenderTargetView(g_mainRenderTargetView, clear_color);
        ImGui_ImplDX11_RenderDrawData(ImGui::GetDrawData());

        g_pSwapChain->Present(1, 0);
    }

    // Cleanup
    ImGui_ImplDX11_Shutdown();
    ImGui_ImplWin32_Shutdown();
    ImGui::DestroyContext();
    CleanupDeviceD3D();
    DestroyWindow(hwnd);
    UnregisterClassW(wc.lpszClassName, wc.hInstance);

    return 0;
}

// ============================================================
// D3D11 HELPERS
// ============================================================

bool CreateDeviceD3D(HWND hWnd) {
    DXGI_SWAP_CHAIN_DESC sd = {};
    sd.BufferCount = 2;
    sd.BufferDesc.Format = DXGI_FORMAT_R8G8B8A8_UNORM;
    sd.BufferUsage = DXGI_USAGE_RENDER_TARGET_OUTPUT;
    sd.OutputWindow = hWnd;
    sd.SampleDesc.Count = 1;
    sd.Windowed = TRUE;
    sd.SwapEffect = DXGI_SWAP_EFFECT_DISCARD;

    D3D_FEATURE_LEVEL featureLevel;
    if (D3D11CreateDeviceAndSwapChain(
        nullptr, D3D_DRIVER_TYPE_HARDWARE, nullptr, 0,
        nullptr, 0, D3D11_SDK_VERSION,
        &sd, &g_pSwapChain, &g_pd3dDevice, &featureLevel, &g_pd3dDeviceContext) != S_OK)
        return false;

    CreateRenderTarget();
    return true;
}

void CleanupDeviceD3D() {
    CleanupRenderTarget();
    if (g_pSwapChain) { g_pSwapChain->Release(); g_pSwapChain = nullptr; }
    if (g_pd3dDeviceContext) { g_pd3dDeviceContext->Release(); g_pd3dDeviceContext = nullptr; }
    if (g_pd3dDevice) { g_pd3dDevice->Release(); g_pd3dDevice = nullptr; }
}

void CreateRenderTarget() {
    ID3D11Texture2D* pBackBuffer;
    g_pSwapChain->GetBuffer(0, IID_PPV_ARGS(&pBackBuffer));
    g_pd3dDevice->CreateRenderTargetView(pBackBuffer, nullptr, &g_mainRenderTargetView);
    pBackBuffer->Release();
}

void CleanupRenderTarget() {
    if (g_mainRenderTargetView) { g_mainRenderTargetView->Release(); g_mainRenderTargetView = nullptr; }
}

LRESULT WINAPI WndProc(HWND hWnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    if (ImGui_ImplWin32_WndProcHandler(hWnd, msg, wParam, lParam))
        return true;

    switch (msg) {
    case WM_SIZE:
        if (g_pd3dDevice && wParam != SIZE_MINIMIZED) {
            CleanupRenderTarget();
            g_pSwapChain->ResizeBuffers(0, (UINT)LOWORD(lParam), (UINT)HIWORD(lParam), DXGI_FORMAT_UNKNOWN, 0);
            CreateRenderTarget();
        }
        return 0;
    case WM_DESTROY:
        PostQuitMessage(0);
        return 0;
    }
    return DefWindowProcW(hWnd, msg, wParam, lParam);
}